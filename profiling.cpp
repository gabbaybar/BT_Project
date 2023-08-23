#include "pin.H"
#include <iostream>
#include <string>
#include <cstdlib>
#include <fstream>
#include <unordered_map>

#define MAX_RTNS 1000
#define MAX_LOOPS 10000
#define MAX_UNCOND_JMPS 10000
#define MAX_CODE_REORDER_JMPS 10
#define MAX_INLINE_RTNS 10
#define HOT_RTNS_TO_OPT 5
using namespace std;
typedef struct routine{
    string name;
    UINT64 icount;
    UINT64 rcount;
    ADDRINT address;
    string img_name;
    ADDRINT img_address;
    ADDRINT hot_call_site;
    ADDRINT hot_call_site_rtn;
    UINT64 hot_call_site_count;
    bool valid;
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
typedef struct call_site{
    ADDRINT caller_addr;
    ADDRINT caller_rtn_addr;
    UINT64 count_calls;
} call_site_t;
typedef struct uncond_forward_jmp{
    ADDRINT rtn_address;
    ADDRINT address;
    UINT64 exec_count;
} uncond_forward_jmp_t;


unordered_map<ADDRINT,loop_t> loops; // will hold loop info
unordered_map<ADDRINT,routine_t> normal_routines; // will hold normal routine info
unordered_map<ADDRINT,routine_t> inline_cand_routines; // will hold inlining candidate routine info
unordered_map<ADDRINT,unordered_map<ADDRINT,call_site_t>> callee_map; // for each rtns, will hold the rtns that call it and how many times
unordered_map<ADDRINT,uncond_forward_jmp_t> uncond_forward_jmps;
vector<call_site_t> hot_rtns_vec;
vector<ADDRINT> rtns_to_translate;
routine_t inline_routines_arr[MAX_RTNS]; //for sorting & exporting purposes
routine_t normal_routines_arr[MAX_RTNS]; //for sorting & exporting purposes
uncond_forward_jmp_t uncond_forward_jmps_arr[MAX_UNCOND_JMPS];
int num_of_inline_rtns;
int num_of_normal_rtns;

// RTN handle
bool rtn_is_valid_for_translation(INS ins, RTN rtn){
    if(INS_IsDirectControlFlow(ins) && INS_IsCall(ins)){
        ADDRINT target_addr = INS_DirectControlFlowTargetAddress(ins);
        if(target_addr == RTN_Address(rtn)){
            cout<<"DEBUG: INS is recursive call to RTN"<<endl;
            return false; // recursive rtn 
        }
    }
    string rtn_name = RTN_Name(rtn);
    if(rtn_name.find("plt") != std::string::npos) return false;
    if(rtn_name.find("bs") != std::string::npos) return false;

    // xed_decoded_inst_t xedd;
    // xed_state_t state;
	// xed_state_zero(&state);
	// state.stack_addr_width=XED_ADDRESS_WIDTH_64b;
    // state.mmode=XED_MACHINE_MODE_LONG_64;
    // xed_decoded_inst_zero_set_mode(&xedd, &state);
    // xed_error_enum_t xed_code = xed_decode(&xedd, reinterpret_cast<UINT8*>(INS_Address(ins)), XED_MAX_INSTRUCTION_BYTES);
    // if (xed_code != XED_ERROR_NONE) {
    //     cerr << "ERROR: xed decode failed for instr at: " << "0x" << hex << INS_Address(ins) << endl;
    //     return false;
    // }
	// unsigned int memops = xed_decoded_inst_number_of_memory_operands(&xedd);

	// //cerr << "Memory Operands" << endl;
	// xed_reg_enum_t base_reg = XED_REG_INVALID;
	// xed_int64_t disp = 0;
	// for(unsigned int i=0; i < memops ; i++)   {
	// 	base_reg = xed_decoded_inst_get_base_reg(&xedd,i);
	// 	disp = xed_decoded_inst_get_memory_displacement(&xedd,i);
    //     if(INS_IsMemoryRead(ins) && (base_reg == XED_REG_RIP)){
    //         ADDRINT memory_target = INS_Address(ins) + INS_Size(ins) + disp;
    //         if((memory_target > INS_Address(RTN_InsTail(rtn))) || (memory_target < INS_Address(RTN_InsHead(rtn)))){
    //             cout<<"DEBUG: INS is MOV outside the scope of the RTN"<<endl;
    //             cout<<INS_Disassemble(ins)<<endl;
    //             return false;
    //         }
    //         //Check if the displacement is out of the function scope
    //     }
    // }

    return true;
}
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
    // vector<instruction_t> rtn_instructions;
    // for(INS ins = RTN_InsHead(rtn) ; ins != INS_Invalid() ; ins = INS_Next(ins)){
    //     instruction_t instruction;
    //     instruction.inst_addr = INS_Address(ins);
    //     instruction.inst_target = 0;
    //     instruction.is_branch = false;
    //     if(INS_IsDirectControlFlow(ins) && !INS_IsCall(ins)){
    //         instruction.inst_target = INS_DirectControlFlowTargetAddress(ins);
    //         instruction.is_branch = true;
    //     }
    //     rtn_instructions.push_back(instruction);

    // }
    //


    // Check if the routine is a good candidate for inlining
    // Candidate for inlining: routine with only 1 RET at the end. (meaning no RET or CALL in the middle of the routine)
    // TODO: add min & max size for candidate routines
    bool candidate_for_inline = true;
    for(INS ins = RTN_InsHead(rtn) ; ins != RTN_InsTail(rtn) ; ins = INS_Next(ins)){
        if(!rtn_is_valid_for_translation(ins,rtn)){
            RTN_Close(rtn);
            return;
        }
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
    routine.valid = true;
    routine.hot_call_site_count = 0;


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

void do_call_count(int *call_count){ (*call_count)++; }
void do_jmp_count(UINT64 *jmp_count){ (*jmp_count)++; }
void Instruction(INS ins, void *v){
    if(INS_IsDirectControlFlow(ins) && INS_IsCall(ins)){
        ADDRINT target_addr = INS_DirectControlFlowTargetAddress(ins);
        ADDRINT ins_addr = INS_Address(ins);
        if(target_addr == RTN_Address(RTN_FindByAddress(ins_addr))) return; // recursive rtn
        if(callee_map.find(target_addr) == callee_map.end()){
            callee_map[target_addr][ins_addr] = {ins_addr , RTN_Address(RTN_FindByAddress(ins_addr)), 0};
        }
        else if(callee_map[target_addr].find(ins_addr) == callee_map[target_addr].end()){
            callee_map[target_addr][ins_addr] = {ins_addr , RTN_Address(RTN_FindByAddress(ins_addr)), 0};
        }
        INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)do_call_count,
                                    IARG_PTR,
                                    &(callee_map[target_addr][ins_addr].count_calls),
                                    IARG_END);
    }
    if(INS_IsDirectControlFlow(ins) && INS_IsBranch(ins) && !INS_HasFallThrough(ins) && 
        (INS_DirectControlFlowTargetAddress(ins) > INS_Address(ins))){
        ADDRINT ins_addr = INS_Address(ins);
        if(uncond_forward_jmps.find(ins_addr) == uncond_forward_jmps.end()){
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)do_jmp_count,
                                    IARG_PTR,
                                    &(uncond_forward_jmps[ins_addr].exec_count),
                                    IARG_END);
        }
        else{
            uncond_forward_jmp_t uncond_jmp;
            uncond_jmp.address = ins_addr;
            uncond_jmp.rtn_address = RTN_Address(RTN_FindByAddress(ins_addr));
            uncond_jmp.exec_count = 0;
            uncond_forward_jmps[ins_addr] = uncond_jmp;
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)do_jmp_count,
                                    IARG_PTR,
                                    &(uncond_forward_jmps[ins_addr].exec_count),
                                    IARG_END);
            
        }
    }
}
// Sort and write RTNs to CSV
int compare_inline_rtn(const void * a, const void * b){
    routine_t *rtn1 = (routine_t*)a;
    routine_t *rtn2 = (routine_t*)b;
    if(rtn1->rcount > rtn2->rcount) return -1;
    else if(rtn1->rcount == rtn2->rcount) return 0;
    return 1;
}
void sort_inline_routines(unordered_map<ADDRINT,routine_t> &routines, routine_t *routines_arr)
{
    int idx= 0;
    for (const auto& info : routines) {
        routines_arr[idx] = info.second;
        idx++;
    }
    qsort(routines_arr,MAX_RTNS,sizeof(routine_t),compare_inline_rtn);
}
int compare_normal_rtn(const void * a, const void * b){
    routine_t *rtn1 = (routine_t*)a;
    routine_t *rtn2 = (routine_t*)b;
    if(rtn1->hot_call_site_count > rtn2->hot_call_site_count) return -1;
    else if(rtn1->hot_call_site_count == rtn2->hot_call_site_count) return 0;
    return 1;
}
void sort_normal_routines(unordered_map<ADDRINT,routine_t> &routines, routine_t *routines_arr)
{
    int idx= 0;
    for (const auto& info : routines) {
        routines_arr[idx] = info.second;
        idx++;
    }
    qsort(routines_arr,MAX_RTNS,sizeof(routine_t),compare_normal_rtn);
}
int compare_uncond_jmps(const void * a, const void * b){
    uncond_forward_jmp_t *jmp1 = (uncond_forward_jmp_t*)a;
    uncond_forward_jmp_t *jmp2 = (uncond_forward_jmp_t*)b;
    if(jmp1->exec_count > jmp2->exec_count) return -1;
    else if(jmp1->exec_count == jmp2->exec_count) return 0;
    return 1;
}
void sort_uncond_jmps(unordered_map<ADDRINT,uncond_forward_jmp_t> &uncond_jmps, uncond_forward_jmp_t *uncond_jmps_arr)
{
    int idx= 0;
    for (const auto& info : uncond_jmps) {
        uncond_jmps_arr[idx] = info.second;
        idx++;
    }
    qsort(uncond_jmps_arr,MAX_UNCOND_JMPS,sizeof(uncond_forward_jmp_t),compare_uncond_jmps);
}
bool rtn_in_hot_rtns(ADDRINT rtn_addr){
    for(unsigned i = 0 ; i< hot_rtns_vec.size() ; i++){
        if(hot_rtns_vec[i].caller_rtn_addr == rtn_addr) return true;
    }
    return false;
}

void write_csv(const string& filename) {
    ofstream ofs = ofstream(filename);
    if (!ofs) {
        cout<<"Cannot open file: " <<filename<<"\n";
        return;
    }
    int normal_rtns_count = 0;
    int inline_rtns_count = 0;
    int code_reorder_jmps_count = 0;
    for (int i = 0; i < MAX_RTNS; i++) {
        if(normal_rtns_count >= HOT_RTNS_TO_OPT) break;
        if(normal_routines_arr[i].hot_call_site_count == 0) break;
        if(normal_routines_arr[i].icount == 0) continue;
        if(normal_routines_arr[i].rcount == 0) continue;
        // if(normal_routines_arr[i].name.find("plt") != std::string::npos) continue;
        if(!rtn_in_hot_rtns(normal_routines_arr[i].address)) continue;
        rtns_to_translate.push_back(normal_routines_arr[i].address);
        normal_rtns_count++;
    }
    for (int i = 0; i < MAX_INLINE_RTNS; i++) {
        if(inline_routines_arr[i].icount == 0) continue;
        if(inline_routines_arr[i].rcount == 0) break;
        // if(inline_routines_arr[i].name.find("plt") != std::string::npos) continue;
        if(inline_routines_arr[i].hot_call_site == 0) continue;
        if(inline_routines_arr[i].valid == false) continue;
        inline_rtns_count++;
    }
    for (int i = 0; i < MAX_UNCOND_JMPS; i++) {
        if(code_reorder_jmps_count >= MAX_CODE_REORDER_JMPS) break;
        if(uncond_forward_jmps_arr[i].exec_count == 0) break;
        if(find(rtns_to_translate.begin(), rtns_to_translate.end(), uncond_forward_jmps_arr[i].rtn_address) == rtns_to_translate.end()) continue;
        code_reorder_jmps_count++;
    }
    ofs << "normal_rtns,"<<normal_rtns_count<<"\n";
    ofs << "img_name,img_address,rtn_name,rtn_address,instruction_count,invoke_count,hot_call_site_calls\n";
    int idx = 0;
    for (int i = 0; i < MAX_RTNS; i++) {
        if(idx >= HOT_RTNS_TO_OPT) break;
        if(normal_routines_arr[i].icount == 0) continue;
        if(normal_routines_arr[i].rcount == 0) break;
        // if(normal_routines_arr[i].name.find("plt") != std::string::npos) continue;
        if(!rtn_in_hot_rtns(normal_routines_arr[i].address)) continue;
        idx++;
        ofs << normal_routines_arr[i].img_name << ",0x" << hex << normal_routines_arr[i].img_address << ","
            << normal_routines_arr[i].name << ",0x" << hex << normal_routines_arr[i].address << ","
            << dec << normal_routines_arr[i].icount << "," << normal_routines_arr[i].rcount << ","
            << dec << normal_routines_arr[i].hot_call_site_count <<"\n";
    }
    ofs << "inline_rtns, "<<inline_rtns_count<<"\n";
    ofs << "img_name,img_address,rtn_name,rtn_address,instruction_count,invoke_count,hot_call_site,caller_rtn,calls\n";
    for (int i = 0; i < MAX_INLINE_RTNS; i++) {
        if(inline_routines_arr[i].icount == 0) continue;
        if(inline_routines_arr[i].rcount == 0) break;
        // if(inline_routines_arr[i].name.find("plt") != std::string::npos) continue;
        if(inline_routines_arr[i].hot_call_site == 0) continue;
        if(inline_routines_arr[i].valid == false) continue;
        ofs << inline_routines_arr[i].img_name << ",0x" << hex << inline_routines_arr[i].img_address << ","
            << inline_routines_arr[i].name << ",0x" << hex << inline_routines_arr[i].address << ","
            << dec << inline_routines_arr[i].icount << "," << inline_routines_arr[i].rcount << ",0x"
            << hex << inline_routines_arr[i].hot_call_site << ",0x"
            << hex << inline_routines_arr[i].hot_call_site_rtn << ","
            << dec << inline_routines_arr[i].hot_call_site_count <<"\n";
    }
    
    ofs << "code_reorder_jmps_count, "<<code_reorder_jmps_count<<"\n";
    ofs << "jmp_address,jmp_rtn_address,exec_count\n";
    idx = 0;
    for (int i = 0; i < MAX_UNCOND_JMPS; i++) {
        if(idx >= MAX_CODE_REORDER_JMPS) break;
        if(uncond_forward_jmps_arr[i].exec_count == 0) break;
        if(find(rtns_to_translate.begin(), rtns_to_translate.end(), uncond_forward_jmps_arr[i].rtn_address) == rtns_to_translate.end()) continue;
        idx++;
        ofs << "0x" << hex << uncond_forward_jmps_arr[i].address << ",0x" 
            << hex << uncond_forward_jmps_arr[i].rtn_address << ", "
            << dec << uncond_forward_jmps_arr[i].exec_count << "\n";
    }
    ofs.close();
}
call_site_t get_hot_call_site(ADDRINT callee_addr){
    //cout<<"Callee: "<<hex<<callee_addr<<endl;
    unordered_map<ADDRINT,call_site_t> callers = callee_map[callee_addr];
    ADDRINT hot_call_site = 0;
    UINT64 hot_call_site_calls = 0;
    for (const auto& caller : callers) {
        //cout<<"Caller: "<<hex<<caller.first<<" Calls: "<<dec<<caller.second<<endl;
        if(caller.second.count_calls > hot_call_site_calls) {
            hot_call_site_calls = caller.second.count_calls;
            hot_call_site = caller.second.caller_addr;
        }
    }
    return callers[hot_call_site];
}
void mark_as_invalid_for_inline(ADDRINT rtn_addr){
    for(int i = 0; i < MAX_RTNS; i++){
        if(inline_routines_arr[i].rcount == 0) return;
        if(inline_routines_arr[i].address == rtn_addr){
            inline_routines_arr[i].valid = false;
            return;
        }
    }
    return; // should never get here...
}
void create_hot_rtns_vec(){
    for (int i = 0; i < MAX_INLINE_RTNS; i++) {
        if(inline_routines_arr[i].icount == 0) continue;
        if(inline_routines_arr[i].rcount == 0) break;
        // if(inline_routines_arr[i].name.find("plt") != std::string::npos) continue;
        if(inline_routines_arr[i].valid == false) continue;
        call_site_t call_site = get_hot_call_site(inline_routines_arr[i].address);
        inline_routines_arr[i].hot_call_site = call_site.caller_addr;
        inline_routines_arr[i].hot_call_site_rtn = call_site.caller_rtn_addr;
        inline_routines_arr[i].hot_call_site_count = call_site.count_calls;
        if(inline_routines_arr[i].hot_call_site == 0) continue;
        hot_rtns_vec.push_back(call_site);
        const ADDRINT inline_rtn_addr = inline_routines_arr[i].address;
        normal_routines.erase(inline_rtn_addr);
        ADDRINT caller_rtn_addr = call_site.caller_rtn_addr;
        normal_routines[caller_rtn_addr].hot_call_site_count = call_site.count_calls;
        mark_as_invalid_for_inline(caller_rtn_addr);
    }
    // for (unsigned i = 0; i <hot_rtns_vec.size(); i++) {
    //     cout<<"hot_rtns_vec callers "<<i<<" = "<<hot_rtns_vec[i].caller_addr<<endl;
    // }
}
//

// FINI
void Fini(INT32 code, void *v){
    sort_uncond_jmps(uncond_forward_jmps,uncond_forward_jmps_arr);
    sort_inline_routines(inline_cand_routines,inline_routines_arr);
    normal_routines.insert(inline_cand_routines.begin(),inline_cand_routines.end());
    create_hot_rtns_vec();
    sort_normal_routines(normal_routines, normal_routines_arr);
    write_csv("rtn-count.csv");
}
// END of FINI

int profiling()
{
    memset(inline_routines_arr,0,sizeof(routine_t)*MAX_RTNS);
    memset(normal_routines_arr,0,sizeof(routine_t)*MAX_RTNS);
    memset(uncond_forward_jmps_arr,0,sizeof(uncond_forward_jmp_t)*MAX_UNCOND_JMPS);
    num_of_inline_rtns = 0;
    num_of_normal_rtns = 0;
    RTN_AddInstrumentFunction(Routine,0);
    INS_AddInstrumentFunction(Instruction,0);
    PIN_AddFiniFunction(Fini,0);
    PIN_StartProgram();
    return 0;
}