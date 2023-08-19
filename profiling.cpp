#include "pin.H"
#include <iostream>
#include <string>
#include <cstdlib>
#include <fstream>
#include <unordered_map>

#define MAX_RTNS 1000
#define MAX_LOOPS 10000
#define MAX_INLINE_RTNS 20
#define HOT_RTNS_TO_OPT 10
using namespace std;
typedef struct routine{
    string name;
    UINT64 icount;
    UINT64 rcount;
    ADDRINT address;
    string img_name;
    ADDRINT img_address;
} routine_t;
typedef struct loop{
    int count_seen;
    int count_loop_invoked;
    ADDRINT rtn_addr;
    //For Diff Count Claculations
    bool first_invoke;
    int last_invocation_iterations;
    int current_invocation_iterations;
    int diff_count;
} loop_t;
typedef struct loop_print{
    ADDRINT loop_target_addr;
    int count_seen;
    int count_loop_invoked;
    double mean_taken;
    int diff_count;
    string routine_name;
    ADDRINT routine_addr;
    int routine_icount;
    int routine_calls;
}loop_print_t;
typedef struct instruction{
    ADDRINT inst_addr;
    ADDRINT inst_target;
    bool is_branch;
} instruction_t;

unordered_map<ADDRINT,loop_t> loops; // will hold loop info
unordered_map<ADDRINT,routine_t> normal_routines; // will hold normal routine info
unordered_map<ADDRINT,routine_t> inline_cand_routines; // will hold inlining candidate routine info
routine_t inline_routines_arr[MAX_RTNS]; //for sorting & exporting purposes
routine_t normal_routines_arr[MAX_RTNS]; //for sorting & exporting purposes
int num_of_inline_rtns;
int num_of_normal_rtns;

// RTN handle
bool ins_is_valid_for_inline(INS ins, RTN rtn){
    if(INS_IsDirectBranch(ins)){
        ADDRINT target = INS_DirectControlFlowTargetAddress(ins);
        if((target > INS_Address(RTN_InsTail(rtn))) || (target < INS_Address(RTN_InsHead(rtn)))){
            cout<<"DEBUG: INS is JMP to outside of RTN scope"<<endl;
            cout<<INS_Disassemble(ins)<<endl;
            cout<<"RTN Head: "<<INS_Address(RTN_InsHead(rtn))<<endl;
            cout<<"RTN Tail: "<<INS_Address(RTN_InsTail(rtn))<<endl;
            return false;
        }
    }
    xed_decoded_inst_t xedd;
    xed_state_t state;
	xed_state_zero(&state);
	state.stack_addr_width=XED_ADDRESS_WIDTH_64b;
    state.mmode=XED_MACHINE_MODE_LONG_64;
    xed_decoded_inst_zero_set_mode(&xedd, &state);
    xed_error_enum_t xed_code = xed_decode(&xedd, reinterpret_cast<UINT8*>(INS_Address(ins)), XED_MAX_INSTRUCTION_BYTES);
    if (xed_code != XED_ERROR_NONE) {
        cerr << "ERROR: xed decode failed for instr at: " << "0x" << hex << INS_Address(ins) << endl;
        return false;
    }
	unsigned int memops = xed_decoded_inst_number_of_memory_operands(&xedd);

	//cerr << "Memory Operands" << endl;
	xed_reg_enum_t base_reg = XED_REG_INVALID;
	xed_int64_t disp = 0;
	for(unsigned int i=0; i < memops ; i++)   {
		base_reg = xed_decoded_inst_get_base_reg(&xedd,i);
		disp = xed_decoded_inst_get_memory_displacement(&xedd,i);
        bool disp_positive = (disp > 0);
        if(INS_IsLea(ins) || INS_IsMov(ins)){
            if ((base_reg == XED_REG_RSP) && !disp_positive) {
                cout<<"DEBUG: INS has negative disp from RSP"<<endl;
                cout<<INS_Disassemble(ins)<<endl;
                return false;
            }
            if ((base_reg == XED_REG_RBP) && disp_positive) {
                cout<<"DEBUG: INS has positive disp from RBP"<<endl;
                cout<<INS_Disassemble(ins)<<endl;
                return false;
            }
        }
        if(INS_IsIndirectControlFlow(ins) && INS_IsBranch(ins)){ // Indir Jump
            if(base_reg == XED_REG_RIP){
                ADDRINT target = INS_Address(ins) + INS_Size(ins) + disp;
                if((target > INS_Address(RTN_InsTail(rtn))) || (target < INS_Address(RTN_InsHead(rtn)))){
                    cout<<"DEBUG: INS is Indir Jump outside the scope of the RTN"<<endl;
                    cout<<INS_Disassemble(ins)<<endl;
                    return false;
                }
            }
            else{
                cout<<"DEBUG: INS is Indir Jump"<<endl;
                cout<<INS_Disassemble(ins)<<endl;
                return false;
            }
        }
	}
    return true;
}
void do_inst_count(int *icount){ (*icount)++; }
void do_rtn_count(int *icount, int *rcount){ 
    (*icount)++;
    (*rcount)++;
}
void Routine(RTN rtn, void *v){
    if(RTN_Valid(rtn) == false)
		return;
    RTN_Open(rtn);
    ADDRINT rtn_addr = RTN_Address(rtn);
    IMG rtn_img=IMG_FindByAddress(rtn_addr);
    if(!IMG_IsMainExecutable(rtn_img)){
        RTN_Close(rtn);
        return;
    }
    //ADDRINT rtn_tail_addr = INS_Address(RTN_InsTail(rtn));
    // Save routine instructions & insert counter increments
    vector<instruction_t> rtn_instructions;
    for(INS ins = RTN_InsHead(rtn) ; ins != INS_Invalid() ; ins = INS_Next(ins)){
        instruction_t instruction;
        instruction.inst_addr = INS_Address(ins);
        instruction.inst_target = 0;
        instruction.is_branch = false;
        if(INS_IsDirectControlFlow(ins) && !INS_IsCall(ins)){
            instruction.inst_target = INS_DirectControlFlowTargetAddress(ins);
            instruction.is_branch = true;
        }
        rtn_instructions.push_back(instruction);
    }
    // Check if the routine is a good candidate for inlining
    // Candidate for inlining: routine with only 1 RET at the end. (meaning no RET or CALL in the middle of the routine)
    // TODO: add min & max size for candidate routines
    bool candidate_for_inline = true;
    for(INS ins = RTN_InsHead(rtn) ; ins != RTN_InsTail(rtn) ; ins = INS_Next(ins)){
        if(!ins_is_valid_for_inline(ins,rtn)){
            candidate_for_inline = false;
            break;
        }
    }
    routine_t routine;
    routine.name = RTN_Name(rtn);
    routine.address = rtn_addr;
    routine.img_name = IMG_Name(rtn_img);
    routine.img_address = IMG_LowAddress(rtn_img);
    routine.icount = 0;
    routine.rcount = 0;

    
    if(candidate_for_inline && INS_IsRet(RTN_InsTail(rtn))){ // Last instruction is RET
        num_of_inline_rtns++;
        inline_cand_routines[rtn_addr] = routine;
        cout<<"Debug: INLINE RTN "<<RTN_Name(rtn)<<endl;
        INS_InsertCall(RTN_InsHead(rtn), IPOINT_BEFORE, (AFUNPTR)do_rtn_count,
                                            IARG_PTR,
                                            &(inline_cand_routines[rtn_addr].icount),
                                            IARG_PTR,
                                            &(inline_cand_routines[rtn_addr].rcount),
                                            IARG_END);
        for(INS ins = INS_Next(RTN_InsHead(rtn)) ; ins != INS_Invalid() ; ins = INS_Next(ins)){
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)do_inst_count,
                                                IARG_PTR,
                                                &(inline_cand_routines[rtn_addr].icount),
                                                IARG_END);
        }
    }
    else{
        num_of_normal_rtns++;
        normal_routines[rtn_addr] = routine;
        cout<<"Debug: Normal RTN"<<RTN_Name(rtn)<<endl;
        INS_InsertCall(RTN_InsHead(rtn), IPOINT_BEFORE, (AFUNPTR)do_rtn_count,
                                            IARG_PTR,
                                            &(normal_routines[rtn_addr].icount),
                                            IARG_PTR,
                                            &(normal_routines[rtn_addr].rcount),
                                            IARG_END);
        for(INS ins = INS_Next(RTN_InsHead(rtn)) ; ins != INS_Invalid() ; ins = INS_Next(ins)){
            // if(!INS_Valid(ins)){
            //     cout<<"Debug: INLINE RTN, Invalid INS"<<endl;
            //     break;
            // }
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)do_inst_count,
                                                IARG_PTR,
                                                &(normal_routines[rtn_addr].icount),
                                                IARG_END);
        }
    }
    RTN_Close(rtn);
}
// end of RTN handle

// Sort and write RTNs to CSV
int compare_rtn(const void * a, const void * b){
    routine_t *rtn1 = (routine_t*)a;
    routine_t *rtn2 = (routine_t*)b;
    if(rtn1->rcount > rtn2->rcount) return -1;
    else if(rtn1->rcount == rtn2->rcount) return 0;
    return 1;
}
void sort_routines(unordered_map<ADDRINT,routine_t> &routines, routine_t *routines_arr)
{
    int idx= 0;
    for (const auto& info : routines) {
        routines_arr[idx] = info.second;
        idx++;
    }
    qsort(routines_arr,MAX_RTNS,sizeof(routine_t),compare_rtn);
}
void write_csv(const string& filename) {
    ofstream ofs = ofstream(filename);
    if (!ofs) {
        cout<<"Cannot open file: " <<filename<<"\n";
        return;
    }
    int normal_rtns_count = 0;
    int inline_rtns_count = 0;
    for (int i = 0; i < HOT_RTNS_TO_OPT; i++) {
        if(normal_routines_arr[i].icount == 0) continue;
        if(normal_routines_arr[i].rcount == 0) break;
        if(normal_routines_arr[i].name.find("plt") != std::string::npos) continue;
        normal_rtns_count++;
    }
    for (int i = 0; i < MAX_INLINE_RTNS; i++) {
        if(inline_routines_arr[i].icount == 0) continue;
        if(inline_routines_arr[i].rcount == 0) break;
        if(inline_routines_arr[i].name.find("plt") != std::string::npos) continue;
        inline_rtns_count++;
    }
    ofs << "normal_rtns,"<<normal_rtns_count<<"\n";
    ofs << "img_name,img_address,rtn_name,rtn_address,instruction_count,invoke_count\n";
    for (int i = 0; i < HOT_RTNS_TO_OPT; i++) {
        if(normal_routines_arr[i].icount == 0) continue;
        if(normal_routines_arr[i].rcount == 0) break;
        if(normal_routines_arr[i].name.find("plt") != std::string::npos) continue;
        ofs << normal_routines_arr[i].img_name << ", 0x" << hex << normal_routines_arr[i].img_address << ","
            << normal_routines_arr[i].name << ", 0x" << hex << normal_routines_arr[i].address << ","
            << dec << normal_routines_arr[i].icount << "," << normal_routines_arr[i].rcount <<"\n";
    }
    ofs << "inline_rtns, "<<inline_rtns_count<<"\n";
    ofs << "img_name,img_address,rtn_name,rtn_address,instruction_count,invoke_count\n";
    for (int i = 0; i < MAX_INLINE_RTNS; i++) {
        if(inline_routines_arr[i].icount == 0) continue;
        if(inline_routines_arr[i].rcount == 0) break;
        if(inline_routines_arr[i].name.find("plt") != std::string::npos) continue;
        ofs << inline_routines_arr[i].img_name << ", 0x" << hex << inline_routines_arr[i].img_address << ","
            << inline_routines_arr[i].name << ", 0x" << hex << inline_routines_arr[i].address << ","
            << dec << inline_routines_arr[i].icount << "," << inline_routines_arr[i].rcount <<"\n";
    }
    ofs.close();
}
//

// FINI
void Fini(INT32 code, void *v){
    sort_routines(inline_cand_routines,inline_routines_arr);
    normal_routines.insert(inline_cand_routines.begin(),inline_cand_routines.end());
    sort_routines(normal_routines, normal_routines_arr);
    write_csv("rtn-count.csv");
}
// END of FINI

int profiling()
{
    memset(inline_routines_arr,0,sizeof(routine_t)*MAX_RTNS);
    memset(normal_routines_arr,0,sizeof(routine_t)*MAX_RTNS);
    num_of_inline_rtns = 0;
    num_of_normal_rtns = 0;
    RTN_AddInstrumentFunction(Routine,0);
    PIN_AddFiniFunction(Fini,0);
    PIN_StartProgram();
    return 0;
}