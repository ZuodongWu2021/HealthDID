//#define DEBUG

#include "../mpc/ot/alsz_ote.hpp"
#include "../crypto/setup.hpp"

struct OTETestcase{
    size_t EXTEND_LEN; 
    std::vector<block> vec_m0; 
    std::vector<block> vec_m1; 


    std::vector<uint8_t> vec_selection_bit; 
    size_t HAMMING_WEIGHT; // number of 1 in vec_selection_bit 
    std::vector<block> vec_result; 
    
    std::vector<block> vec_m; 
    std::vector<block> vec_one_sided_result; 
}; 

OTETestcase GenTestCase(size_t EXTEND_LEN)
{	
    OTETestcase testcase; 
    testcase.EXTEND_LEN = EXTEND_LEN; 
    testcase.HAMMING_WEIGHT = 0; 

	PRG::Seed seed = PRG::SetSeed(fixed_seed, 0); // initialize PRG
	
    testcase.vec_m0 = PRG::GenRandomBlocks(seed, EXTEND_LEN);
	testcase.vec_m1 = PRG::GenRandomBlocks(seed, EXTEND_LEN);
	testcase.vec_selection_bit = PRG::GenRandomBits(seed, EXTEND_LEN);
    testcase.vec_m  = PRG::GenRandomBlocks(seed, EXTEND_LEN);
    // for(i = 0; i < EXTEND_LEN; i++){
    //     vec_z.emplace_back(std::vector<uint8_t>(vec_m[i].data(), vec_m[i].data()+16));
    // }


	for (auto i = 0; i < EXTEND_LEN; i++){
		if(testcase.vec_selection_bit[i] == 0){
            testcase.vec_result.emplace_back(testcase.vec_m0[i]);
        } 
		else{
            testcase.vec_result.emplace_back(testcase.vec_m1[i]);
            testcase.HAMMING_WEIGHT++; 
            testcase.vec_one_sided_result.emplace_back(testcase.vec_m[i]);
            // testcase.vec_z_one_sided_result.emplace_back(testcase.vec_z[i]);
        } 
	}
    return testcase;
}

void SaveTestCase(OTETestcase &testcase, std::string testcase_filename)
{
    std::ofstream fout; 
    fout.open(testcase_filename, std::ios::binary); 
    if(!fout)
    {
        std::cerr << testcase_filename << " open error" << std::endl;
        exit(1); 
    }
    fout << testcase.EXTEND_LEN; 
    fout << testcase.HAMMING_WEIGHT; 

    fout << testcase.vec_m0; 
    fout << testcase.vec_m1; 
    fout << testcase.vec_selection_bit; 
    fout << testcase.vec_result; 
    fout << testcase.vec_m; 
    fout << testcase.vec_one_sided_result;  

    // fout << testcase.vec_z; 
    // fout << testcase.vec_z_one_sided_result; 

    fout.close(); 
}

void FetchTestCase(OTETestcase &testcase, std::string testcase_filename)
{
    std::ifstream fin; 
    fin.open(testcase_filename, std::ios::binary); 
    if(!fin)
    {
        std::cerr << testcase_filename << " open error" << std::endl;
        exit(1); 
    }
    fin >> testcase.EXTEND_LEN; 
    fin >> testcase.HAMMING_WEIGHT; 
	testcase.vec_m0.resize(testcase.EXTEND_LEN); 
	testcase.vec_m1.resize(testcase.EXTEND_LEN); 
	testcase.vec_selection_bit.resize(testcase.EXTEND_LEN); 
	testcase.vec_result.resize(testcase.EXTEND_LEN); 

    testcase.vec_m.resize(testcase.EXTEND_LEN); 
    testcase.vec_one_sided_result.resize(testcase.HAMMING_WEIGHT); 

    // testcase.vec_z.resize(testcase.EXTEND_LEN); 
    // testcase.vec_z_one_sided_result.resize(testcase.HAMMING_WEIGHT); 

    fin >> testcase.vec_m0; 
    fin >> testcase.vec_m1; 
    fin >> testcase.vec_selection_bit; 
	fin >> testcase.vec_result; 
    fin >> testcase.vec_m; 
    fin >> testcase.vec_one_sided_result; 

    // fin >> testcase.vec_z; 
    // fin >> testcase.vec_z_one_sided_result; 

    fin.close(); 
}

int main()
{
	CRYPTO_Initialize(); 

	PrintSplitLine('-'); 
    std::cout << "ALSZ OTE test begins >>>" << std::endl; 
    PrintSplitLine('-'); 
    std::cout << "generate or load public parameters and test case" << std::endl;

    // generate pp (must be same for both server and client)
    std::string pp_filename = "alszote.pp"; 
    ALSZOTE::PP pp; 
    size_t BASE_LEN = 128; 
    if(!FileExist(pp_filename)){
        pp = ALSZOTE::Setup(BASE_LEN); 
        ALSZOTE::SavePP(pp, pp_filename); 
    }
    else{
        ALSZOTE::FetchPP(pp, pp_filename);
    }

    // set instance size
    size_t EXTEND_LEN = size_t(pow(2, 20)); 
    std::cout << "LENGTH of OTE = " << EXTEND_LEN << std::endl; 

    // generate or fetch test case
    std::string testcase_filename = "alszote.testcase"; 
    OTETestcase testcase; 
    if(!FileExist(testcase_filename)){
        testcase = GenTestCase(EXTEND_LEN); 
        SaveTestCase(testcase, testcase_filename); 
    }
    else{
        FetchTestCase(testcase, testcase_filename);
    }

    std::string party;
    std::cout << "please select your role between (one-sided) sender and (one-sided) receiver (hint: start sender first) ==> ";  
    std::getline(std::cin, party); // first sender (acts as server), then receiver (acts as client)
	
    if(party == "sender"){
        NetIO server_io("server", "", 8080); 
	    ALSZOTE::Send(server_io, pp, testcase.vec_m0, testcase.vec_m1, EXTEND_LEN);
    }

    if(party == "receiver"){
        NetIO client_io("client", "127.0.0.1", 8080); 

	    std::vector<block> vec_result_prime = ALSZOTE::Receive(client_io, pp, testcase.vec_selection_bit, EXTEND_LEN);
        
        if(Block::Compare(testcase.vec_result, vec_result_prime) == true){
			std::cout << "two-sided ALSZ OTE test succeeds" << std::endl; 
		} 
        else{
            std::cout << "two-sided ALSZ OTE test fails" << std::endl;  
        }
    }

    if(party == "one-sided sender"){
        NetIO server_io("server", "", 8080); 
	    ALSZOTE::OnesidedSend(server_io, pp, testcase.vec_m, testcase.vec_m1,EXTEND_LEN,EXTEND_LEN);
    }

    if(party == "one-sided receiver"){
        NetIO client_io("client", "127.0.0.1", 8080); 
	    std::vector<block> vec_one_sided_result_prime = 
        ALSZOTE::OnesidedReceive(client_io, pp, testcase.vec_selection_bit, EXTEND_LEN);
        
        if(Block::Compare(testcase.vec_one_sided_result, vec_one_sided_result_prime) == true){
			std::cout << "one-sided ALSZ OTE test succeeds" << std::endl; 
		} 
        else{
            std::cout << "one-sided ALSZ OTE test fails" << std::endl;  
        }
    }
	
    std::vector<std::vector<uint8_t>> vec_z; 
    for(auto i = 0; i < EXTEND_LEN; i++){
        // vec_z.emplace_back(std::vector<uint8_t>((uint8_t*)testcase.vec_m[i].data(), 
        //                    (uint8_t*)testcase.vec_m[i].data()+16);
        vec_z.emplace_back(std::vector<uint8_t>(16, '0'));
    }
    
    if(party == "z-one-sided-sender"){
        NetIO server_io("server", "", 8080); 
	    ALSZOTE::OnesidedSendByteVector(server_io, pp, vec_z, EXTEND_LEN);
    }

    if(party == "z-one-sided-receiver"){
        NetIO client_io("client", "127.0.0.1", 8080); 
	    std::vector<std::vector<uint8_t>> vec_z_one_sided_result_prime = 
        ALSZOTE::OnesidedReceiveByteVector(client_io, pp, testcase.vec_selection_bit, EXTEND_LEN);
       
        // if(Block::Compare(testcase.vec_one_sided_result, vec_one_sided_result_prime) == true){
		// 	std::cout << "one-sided ALSZ OTE test succeeds" << std::endl; 
		// } 
        // else{
        //     std::cout << "one-sided ALSZ OTE test fails" << std::endl;  
        // }
    }


    PrintSplitLine('-'); 
    std::cout << "ALSZ OTE test ends >>>" << std::endl; 
    PrintSplitLine('-'); 

    CRYPTO_Finalize();   
	return 0; 
}