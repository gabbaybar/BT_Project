#include "rtn-translation.cpp"
#include "profiling.cpp"
#include "pin.H"
#include <unordered_map>
#include <algorithm>
#include <vector>
#include <string>
#include <iostream>
#include <sstream>
#include <fstream>


KNOB<BOOL> Prof(KNOB_MODE_WRITEONCE,    "pintool","prof", "0", "run exercise 2 and print out loop trip count information into the file loop-count.csv according to the instructions of exercise 2");
KNOB<BOOL> Opt(KNOB_MODE_WRITEONCE,    "pintool","opt", "0", "run in probe mode and generate the binary code of the top 10 routines (based on total dynamic count of the instructions in the routine) according to the gathered profiling data from previous run");
using namespace std;

void split_delim(string s, char del, vector<string> &res)
{
    stringstream ss(s);
    string word;
    while (!ss.eof()) {
        getline(ss, word, del);
        res.push_back(word);
    }
}
void get_data_from_csv(){
    fstream rtn_count_file;
    rtn_count_file.open("rtn-count.csv", ios::in);
    if(rtn_count_file.fail()){
        printf("rtn-count.csv file does not exist! please run the pintool again with -prof\n");
        return;
    }
    string line;
    // Go over the CSV line by line
    getline(rtn_count_file, line); // First row - hot rtns
    vector<string> hot_rtns_splitted_line;
    split_delim(line, ',',hot_rtns_splitted_line);
    istringstream iss_num_of_rtns(hot_rtns_splitted_line[1]);
    int num_of_rtns;
    iss_num_of_rtns >> num_of_rtns;
    //cout<<"Num of normal RTNS: "<<num_of_rtns<<endl;
    getline(rtn_count_file, line); // Thorwing away the first line (headers)
    for(int i=0 ; i < num_of_rtns ; i++){
        // Parse the CSV file and extract rtn_address & icount
        getline(rtn_count_file, line);
        vector<string> splitted_line;
        split_delim(line, ',',splitted_line);
        ADDRINT rtn_addr;
        string raw_rtn_addr = splitted_line[3];
        string no_hex_rtn_addr = raw_rtn_addr.substr(3,raw_rtn_addr.length());
        stringstream ss;
        ss << hex << no_hex_rtn_addr;
        ss >> rtn_addr;
		// end parsing
        //cout<<"RTN ADDR: "<<hex<<rtn_addr<<endl;
        hot_rtns.push_back(rtn_addr); // RTN is valid, in the top of the CSV and Main Executable - HOT RTN
    }
    num_of_rtns = 0;
    getline(rtn_count_file, line); // First row - inline candidate rtns
    vector<string> inline_rtns_splitted_line;
    split_delim(line, ',',inline_rtns_splitted_line);
    istringstream iss2_num_of_rtns(inline_rtns_splitted_line[1]);
    iss2_num_of_rtns >> num_of_rtns;
    // cout<<inline_rtns_splitted_line[0]<<endl;
    // cout<<"Num of inline candidate RTNS: "<< dec <<num_of_rtns<<endl;
    getline(rtn_count_file, line); // Thorwing away the first line (headers)
    for(int i=0 ; i < num_of_rtns ; i++){
        // Parse the CSV file and extract rtn_address & icount
        getline(rtn_count_file, line);
        vector<string> splitted_line;
        split_delim(line, ',',splitted_line);
        ADDRINT rtn_addr;
        string raw_rtn_addr = splitted_line[3];
        string no_hex_rtn_addr = raw_rtn_addr.substr(3,raw_rtn_addr.length());
        stringstream ss;
        ss << hex << no_hex_rtn_addr;
        ss >> rtn_addr;
        inline_cand_rtns.push_back(rtn_addr); 
        
        ADDRINT call_site;
        string raw_call_site = splitted_line[6];
        string no_hex_call_site = raw_call_site.substr(3,raw_call_site.length());
        stringstream ss_call_site;
        ss_call_site << hex << no_hex_call_site;
        ss_call_site >> call_site;
        //cout<<"RTN ADDR: "<<hex<<rtn_addr<<endl;
        hot_call_sites.push_back(call_site);
    }
    cout<<"DEBUG: Hot Call Sites"<<endl;
    for(auto& caller : hot_call_sites){
        cout<<hex<<caller<<endl;
    }
    rtn_count_file.close();
    //end of CSV data extraction
}
int main(int argc, char * argv[])
{
    PIN_InitSymbols();
    PIN_Init(argc, argv);
    if(Prof) // Run the profiling function
        profiling();
    else if(Opt){
        get_data_from_csv();
        rtn_translaion_main(argc, argv);
    }
    else
        PIN_StartProgram();
    return 0;
}