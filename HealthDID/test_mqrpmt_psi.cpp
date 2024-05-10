#include "../mpc/pso/mqrpmt_psi.hpp"
#include "../crypto/setup.hpp"
#include "../crypto/ec_point.hpp"
#include "../crypto/ec_group.hpp"
#include "../commitment/pedersen.hpp"
#include <cstdlib>
#include <string>
#include <openssl/sha.h>
#include <iostream> 
#include <math.h>
#include <fstream> 
#include <map>
#include "../signature/schnorr.hpp"
using namespace std;
struct TestCase{
    size_t LOG_SENDER_LEN; 
    size_t LOG_RECEIVER_LEN; 
    size_t SENDER_LEN; 
    size_t RECEIVER_LEN; 
    std::vector<block> vec_X; // sender's set
    std::vector<block> vec_Y; // receiver's set
    std::vector<block> vec_D; // user's value
    size_t HAMMING_WEIGHT; // cardinality of intersection
    std::vector<uint8_t> vec_indication_bit; // X[i] = Y[i] iff b[i] = 1 

    std::vector<block> vec_intersection; // for PSI 

};

// LEN is the cardinality of two sets
TestCase GenTestCase(size_t LOG_SENDER_LEN, size_t LOG_RECEIVER_LEN)
{
    TestCase testcase;

    testcase.LOG_SENDER_LEN = LOG_SENDER_LEN; 
    testcase.LOG_RECEIVER_LEN = LOG_RECEIVER_LEN; 
    testcase.SENDER_LEN = size_t(pow(2, testcase.LOG_SENDER_LEN));  
    testcase.RECEIVER_LEN = size_t(pow(2, testcase.LOG_RECEIVER_LEN)); 

    PRG::Seed seed = PRG::SetSeed(nullptr, 0); // initialize PRG
    testcase.vec_X = PRG::GenRandomBlocks(seed, testcase.SENDER_LEN);
    testcase.vec_Y = PRG::GenRandomBlocks(seed, testcase.RECEIVER_LEN);
    testcase.vec_D = PRG::GenRandomBlocks(seed, testcase.SENDER_LEN);

    // set the Hamming weight to be a half of the max possible intersection size
    testcase.HAMMING_WEIGHT = std::min(testcase.SENDER_LEN, testcase.RECEIVER_LEN)/2;

    // generate a random indication bit vector conditioned on given Hamming weight
    testcase.vec_indication_bit.resize(testcase.SENDER_LEN);  
    for(auto i = 0; i < testcase.SENDER_LEN; i++){
        if(i < testcase.HAMMING_WEIGHT) testcase.vec_indication_bit[i] = 1; 
        else testcase.vec_indication_bit[i] = 0; 
    }
    std::shuffle(testcase.vec_indication_bit.begin(), testcase.vec_indication_bit.end(), global_built_in_prg);

    // adjust vec_X and vec_Y
    for(auto i = 0, j = 0; i < testcase.SENDER_LEN; i++){
        if(testcase.vec_indication_bit[i] == 1){
            testcase.vec_X[i] = testcase.vec_Y[j];
            testcase.vec_intersection.emplace_back(testcase.vec_Y[j]); 
            j++; 
        }
    }

    std::shuffle(testcase.vec_Y.begin(), testcase.vec_Y.end(), global_built_in_prg);

    return testcase; 
}

void PrintTestCase(TestCase testcase)
{
    PrintSplitLine('-'); 
    std::cout << "TESTCASE INFO >>>" << std::endl;
    std::cout << "Sender's set size = " << testcase.SENDER_LEN << std::endl;
    std::cout << "Receiver's set size = " << testcase.RECEIVER_LEN << std::endl;
    std::cout << "Intersection cardinality = " << testcase.HAMMING_WEIGHT << std::endl; 
    PrintSplitLine('-'); 
}

void SaveTestCase(TestCase &testcase, std::string testcase_filename)
{
    std::ofstream fout; 
    fout.open(testcase_filename, std::ios::binary); 
    if(!fout)
    {
        std::cerr << testcase_filename << " open error" << std::endl;
        exit(1); 
    }

    fout << testcase.LOG_SENDER_LEN; 
    fout << testcase.LOG_RECEIVER_LEN; 
    fout << testcase.SENDER_LEN; 
    fout << testcase.RECEIVER_LEN; 
    fout << testcase.HAMMING_WEIGHT; 
     
    fout << testcase.vec_X; 
    fout << testcase.vec_Y; 
    fout << testcase.vec_D; 
    fout << testcase.vec_indication_bit;
    fout << testcase.vec_intersection; 

    fout.close(); 
}

void FetchTestCase(TestCase &testcase, std::string testcase_filename)
{
    std::ifstream fin; 
    fin.open(testcase_filename, std::ios::binary); 
    if(!fin)
    {
        std::cerr << testcase_filename << " open error" << std::endl;
        exit(1); 
    }

    fin >> testcase.LOG_SENDER_LEN; 
    fin >> testcase.LOG_RECEIVER_LEN; 
    fin >> testcase.SENDER_LEN; 
    fin >> testcase.RECEIVER_LEN;
    fin >> testcase.HAMMING_WEIGHT; 

    testcase.vec_X.resize(testcase.SENDER_LEN); 
    testcase.vec_Y.resize(testcase.RECEIVER_LEN); 
    testcase.vec_D.resize(testcase.SENDER_LEN); 
    testcase.vec_indication_bit.resize(testcase.SENDER_LEN); 
    testcase.vec_intersection.resize(testcase.HAMMING_WEIGHT);   

    fin >> testcase.vec_X; 
    fin >> testcase.vec_Y; 
    fin >> testcase.vec_D; 
    fin >> testcase.vec_indication_bit;
    fin >> testcase.vec_intersection; 

    fin.close(); 
}
std::string sha256(const std::string& str) {
    EVP_MD_CTX *mdctx;
    const EVP_MD *md;
    unsigned char md_value[EVP_MAX_MD_SIZE];
    unsigned int md_len;

    md = EVP_sha256();
    mdctx = EVP_MD_CTX_new();
    EVP_DigestInit_ex(mdctx, md, NULL);
    EVP_DigestUpdate(mdctx, str.c_str(), str.length());
    EVP_DigestFinal_ex(mdctx, md_value, &md_len);
    EVP_MD_CTX_free(mdctx);

    char hex[2 * md_len + 1];
    for (unsigned int i = 0; i < md_len; ++i) {
        sprintf(&hex[i * 2], "%02x", md_value[i]);
    }

    return std::string(hex, 2 * md_len);
}
/*void string_multiply(string num1, uint8_t num2) {
        size_t n1 = num1.size(), n2 = num2.size();
        uint8_t ans(n1 + n2, '0');
        
        for(auto  i = n1 - 1; i >= 0; i--) {
        	for(int j = n2 - 1; j >= 0; j--) {
        		int temp = (ans[i + j + 1] - '0') + (num1[i] - '0') * (num2[j] - '0');
        		ans[i + j + 1] = temp % 10 + '0';
        		ans[i + j] += temp / 10;
        	}
        }
        
        for(int i = 0; i < n1 + n2; i++) {
        	if (ans[i] != '0') return ans.substr(i);
        }
        
    
     }*/
     string stringAdd(string num1,string num2){
        int i = num1.size()-1,j = num2.size()-1,add = 0;
        string ans = "";
        while(i >= 0 || j >= 0 || add != 0){
            int x = i >= 0 ? num1[i] - '0' : 0;
            int y = j >= 0 ? num2[j] - '0' : 0;//转数字
            int sum = x + y + add;//按位相加
            ans.push_back(sum % 10 + '0');//+‘0’转string
            add = sum / 10;//进位
            j--;
            i--;
        }
        reverse(ans.begin(),ans.end()); 
        return ans;
    }

     string multiply(string num1, uint8_t* num22) {
        //string num1( (char *) num11);
        string num2( (char *) num22);
        if(num1 == "0" || num2 == "0"){
            return "0";
        }
        string ans = "";
        int n1 = num1.size(), n2 = num2.size();
        for(int i = n2 -1; i >= 0; i--){//遍历num2的每一位，分别与num1的每一位相乘
            string cur;//保存num2中的一位和num1相乘的结果
            int add = 0;//进位
            for(int j = n2-1; j > i; j--){
                cur.push_back('0');//除了最低位以外，其余的每一位的运算结果都需要补0,
            }
            for(int k = n1 - 1; k >= 0; k--){//挨个相乘
                int product = (num1[k] - '0') * (num2[i] - '0') + add;//转数字相乘
                cur.push_back(product % 10 + '0');//转string再push进cur
                add = product / 10;//进位
            }
            if(add != 0){
                cur.push_back(add  + '0');
                //add = add / 10;
            }
            reverse(cur.begin(), cur.end());
            ans = stringAdd(ans, cur);//把num2中的每一位和num1相乘的结果（cur），加起来
        }
    
        return ans;    
    }

string string_to_hex(const string& str) //transfer string to hex-string
{
    string result="0x";
    string tmp;
    stringstream ss;
    for(int i=0;i<str.size();i++)
    {
        ss<<hex<<int(str[i])<<endl;
        ss>>tmp;
        result+=tmp;
    }
    return result;
}

struct PP
{
    ECPoint g; 
    std::vector<ECPoint> vec_h;  
    size_t N_max; 
};

PP Setup (size_t N_max)
{ 
    PP pp;
    pp.N_max = N_max;
    pp.g = ECPoint(generator); 
    /* 
    ** warning: the following method is ad-hoc and insafe cause it is not transparent
    ** we left a secure hash to many points mapping as the future work   
    */
    pp.vec_h = GenRandomECPointVector(N_max); 
    return pp; 
}
void Split(const std::string& src, const std::string& separator, std::vector<std::string>& dest) //字符串分割到数组
{
 
        //参数1：要分割的字符串；参数2：作为分隔符的字符；参数3：存放分割后的字符串的vector向量
 
	string str = src;
	string substring;
	string::size_type start = 0, index;
	dest.clear();
	index = str.find_first_of(separator,start);
	do
	{
		if (index != string::npos)
		{    
			substring = str.substr(start,index-start );
			dest.push_back(substring);
			start =index+separator.size();
			index = str.find(separator,start);
			if (start == string::npos) break;
		}
	}while(index != string::npos);
 
	//the last part
	substring = str.substr(start);
	dest.push_back(substring);
}

BigInt eLGamalEnc(PP &com_pp,ECPoint &X,ECPoint &Y, ECPoint userpk,ECPoint recoverpk){
    BigInt u = GenRandomBigIntLessThan(order); 
    X = com_pp.g*u;
    Y = recoverpk*u+userpk;
    return u;
}
ECPoint elGamalDec(BigInt recoversk, ECPoint X, ECPoint Y){
    ECPoint realsigner = Y-X*recoversk;
    return realsigner;
}
void string2map(const string &pA,map<int, int> &map_pA)
{
	string A = pA;

	for(int i = 0; i<A.size();i++)
	{
		if(A[i]=='('||A[i]==','||A[i]==')')
		{
			A[i]=' ';
		
		}	
	}
	//cout<<A<<endl;
	stringstream ss;
	ss << A;
	int temp;
	vector<int> A_string2_int;
	while(ss>>temp)
	{
		//cout << temp <<endl;
		A_string2_int.push_back(temp);

	}
	for(int j = 0; j <(int)A_string2_int.size()-1;j = j+2)
	{
		map_pA[A_string2_int[j+1]] = A_string2_int[j];	
	}
}
string multiplyPolynormial(const string &pA,const string &pB)
{
	map<int, int> map_pA; 
	map<int, int> map_pB; 
	map<int, int> map_ANS; //存放当前pA项乘以pB的结果
	map<int, int> map_ANS_total; //幂次相同的相加，为最终结果

	vector<int>map_ANS_total2vector;

	string2map(pA,map_pA);//string 存入map中 key:幂数，value：当前幂数的系数
	string2map(pB,map_pB);

	int n =  map_pA.size()+map_pB.size() + 1;

	for(int k = 0; k <n;k++ )//map初始化
	{
		map_ANS.insert(pair<int,int>(k,0));
		map_ANS_total.insert(pair<int,int>(k,0));
	
	
	}
	
	for(int i = 0; i < map_pA.size(); i++)
	{
		for(int j = 0; j < map_pB.size();j++ )
		{
			map_ANS[i+j] = map_pA[i]*map_pB[j];   
			map_ANS_total[i+j] = map_ANS_total[i+j] + map_ANS[i+j]; 
		
		}
			
	}

	//cout<<"the size of map_ANS_total is :"<<map_ANS_total.size()<<endl;
	int count = map_ANS_total.size();
	string answer;

	for(int m = 0; m < map_ANS_total.size();m++)//map转为string
	{
		count--;
		if(map_ANS_total[count]!=0)
		{
			char str[1000];
			sprintf(str,"(%d,%d)",map_ANS_total[count],count);
			//cout<<map_ANS_total[count]<<"  "<<count<<endl;
			answer = answer + str;
		}	
	}
	//cout<<answer<<endl;
	return answer;	
}
vector<vector<int> > shizhuaner(int n,int m){
    int i = 0;
    vector<vector<int> > binary(m,vector<int>(n));
    for(int i = 0;i<m;i++){
    	vector<int> t(n);
    	if(i==0){
    		for(int j = 0;j<n;j++){
    			binary[i][j] = 0;
			}
		}
		else{
			int temp = i;
			int j = 0;
    		for( j =0; temp>0; j++)    
    		{    
       			binary[i][j] =temp%2;   
        		temp = temp/2;   
    		}  	
			for(int h = j;j<n;j++){
				binary[i][j] =0;
			}		
		}

	}
    return binary;
}
void functionring(){
    auto start = std::chrono::steady_clock::now();
    CRYPTO_Initialize(); 
    PP com_pp = Setup(128);
    int m=8;
	int n = log(m)/log(2);
    int index = 2;
    int len0 = 0;
    vector<BigInt> usk(m);   //user's sk
    vector<ECPoint> upk(m+1);  //user's pk
    //keyGen(com_pp,m,usk,upk,index);
    string qianming = "";
    for(int i = 0;i<index;i++){
        BigInt sk_user_int = GenRandomBigIntLessThan(order);
        ECPoint pk_user = com_pp.g*sk_user_int;
        usk[i]=sk_user_int;
        upk[i]=pk_user;
    }
    BigInt sk_user_int = GenRandomBigIntLessThan(order);
    ECPoint p = com_pp.g*sk_user_int;
    usk[index]=sk_user_int;
    upk[index]=p;
    for(int i = index+1;i<m;i++){
        BigInt sk_user_int = GenRandomBigIntLessThan(order);
        ECPoint pk_user = com_pp.g*sk_user_int;
        usk[i]=sk_user_int;
        upk[i]=pk_user;
    }

    upk[m]=com_pp.g;
    BigInt signersk = usk[index];
    ECPoint signerpk = upk[index];
    string E = sha256(signerpk.ToByteString());
    ECPoint ecp_E = Hash::StringToECPoint(E);
    ECPoint T = ecp_E*signersk;
    len0+=T.ToByteString().length();
    
    BigInt sk_recover_int = GenRandomBigIntLessThan(order);
    ECPoint pk_recover = com_pp.g*sk_recover_int;
    
    ECPoint X;
    ECPoint Y;
    BigInt u = eLGamalEnc(com_pp,X,Y,signerpk,pk_recover);
    qianming+=X.ToHexString();
    qianming+=Y.ToHexString();
    len0+=X.ToByteString().length();
    len0+=Y.ToByteString().length();

    vector<vector<int> > binary;
	binary = shizhuaner(n,m);
	int temp = 0;
	for(int j = 0;j<m;j++){
		for (int i = 0; i < n/2; ++i) {
        	temp = binary[j][n-i-1];
        	binary[j][n-i-1] = binary[j][i];
       	 	binary[j][i] = temp;
    	}		
	}

    vector<BigInt> rjs(n);
    vector<int> ajs(n);
    vector<BigInt> sjs(n);
    vector<BigInt> tjs(n);
    vector<int> rouks(n);
    vector<int> lj(n); // index = 2 binary= 10
    vector<int> ljaj(n); 
    for(int i = 0;i<n;i++){
        lj[i] = binary[index][i];
    }
     //genRandomNumber(n,rjs,ajs,sjs,tjs,rouks,ljaj,lj);
    for(int j = 0;j<n;j++){
       BigInt rj_one = GenRandomBigIntLessThan(order); 
       rjs[j] = rj_one;
       int aj_one = rand()%10;
       ajs[j] = aj_one;
       BigInt sj_one = GenRandomBigIntLessThan(order);
       sjs[j] = sj_one;
       BigInt tj_one = GenRandomBigIntLessThan(order);
       tjs[j] = tj_one;
       int rouk_one = rand()%10;
       rouks[j] = rouk_one;
    }
    for(int g = 0;g<n;g++){
        if(lj[g] ==0){
        ljaj[g] = 0;
        }
        else{
            ljaj[g] = ajs[g];
        }
    }

    std::vector<ECPoint> Pederson_commitments_lj(n);
    std::vector<ECPoint> Pederson_commitments_aj(n);
    std::vector<ECPoint> Pederson_commitments_bj(n);
    int len = 0;
    for(int h = 0;h<n;h++){
        
    if(lj[h]==0){
        Pederson_commitments_lj[h] = com_pp.g*rjs[h];
        
        len += Pederson_commitments_lj[h].ToByteString().length();
        qianming+=Pederson_commitments_lj[h].ToHexString();
    }
    else{
        Pederson_commitments_lj[h] = com_pp.g*rjs[h]+com_pp.g*2;
        len += Pederson_commitments_lj[h].ToByteString().length();
        qianming+=Pederson_commitments_lj[h].ToHexString();
    }
    BigInt ajst = ajs[h];
    Pederson_commitments_aj[h] = com_pp.g*sjs[h]+com_pp.g*2*ajst;
    len += Pederson_commitments_aj[h].ToByteString().length();
    qianming+=Pederson_commitments_aj[h].ToHexString();
   
    BigInt ljajt = ljaj[h];
    Pederson_commitments_bj[h] = com_pp.g*tjs[h]+com_pp.g*2*ljajt;
    len += Pederson_commitments_bj[h].ToByteString().length();
    qianming+=Pederson_commitments_bj[h].ToHexString();
    }
    
    vector<vector<int> > Pi;
    for(int i = 0;i<m;i++){
		vector<int> temp;
		for(int j = 0;j<n;j++){
			temp.push_back(0);
		}
		Pi.push_back(temp);
	}
    for(int i = 0;i<m;i++){
		string A = "";
		if(binary[i][0]==1){
			if(binary[index][0]==1){
				A="(1,1),("+to_string(ajs[0])+",0)";				
			}
			else{
				A="(0,0),("+to_string(ajs[0])+",0)";					
			}
		}
		else{
			if(binary[index][0]==0){
				A="(1,1),(-"+to_string(ajs[0])+",0)";				
			}
			else{
				A="(0,0),(-"+to_string(ajs[0])+",0)";
			}
		}
		for(int j = 1;j<n;j++){
			string B = "";
			if(binary[i][j]==1){
				if(binary[index][j]==1){
					B="(1,1),("+to_string(ajs[j])+",0)";
				}
				else{
					B="(0,0),("+to_string(ajs[j])+",0)";
				}
				
			}
			else{
				if(binary[index][j]==0){
					B="(1,1),(-"+to_string(ajs[j])+",0)";					
				}
				else{
					B="(0,0),(-"+to_string(ajs[j])+",0)";					
				}
			}
			A = multiplyPolynormial(A,B);
		}
		//chuli(A,i,n);
        string AA="";
	    int size = 0;
	    for(int i = 0;i<A.size();i++){
		    if(A[i]=='('||A[i]==')')
		    {
			    if(A[i]==')'&&(i+1)<A.size()){
				    AA+=",";
			    }
			else{
				AA+="";				
			}
			size++;
		    }
		    else{
		    	AA+=A[i];
		    }
	    }
	    vector<string> dest(size);
	     Split(AA,",",dest);
	     for(int ti = 0;ti<size;ti+=2){
	 	     int z = atoi(dest[ti+1].c_str());

	 	    if(z!=n){
                int d = atoi(dest[ti].c_str());
	 		    Pi[i][z]=d;
	 	    }
	    }
    }

    int x = rand();
    std::vector<int> fj(n);
    std::vector<BigInt> zaj(n);
    std::vector<BigInt> zbj(n);
    for(int j = 0;j<n;j++){
        if(lj[j] == 0){
           fj[j] = ajs[j];
        }
        else{
            fj[j] = x+ajs[j];
        }
        len += to_string(fj[j]).length();
        
        zaj[j] = rjs[j]*x+sjs[j];
        len += zaj[j].ToByteString().length();
        qianming+=zaj[j].ToHexString();
        zbj[j] = rjs[j]*(x-fj[j])+tjs[j];
        len += zbj[j].ToByteString().length();
        qianming+=zbj[j].ToHexString();
    }
    //cout<<"Ring "<<qianming<<endl;
    auto end = std::chrono::steady_clock::now();
    std::cout << "GenLRRS"
              << ":" << std::chrono::duration<double, std::milli>(end - start).count() << " ms" << std::endl;
    auto start1 = std::chrono::steady_clock::now();
std::cout << "正在验证签名" << std::endl; 
 
    std::vector<ECPoint> zuo1(n);
    std::vector<ECPoint> you1(n);


    std::vector<int> fjij(m);
    for(int i =0;i<m;i++){
        int t = 0;
        if(binary[i][0]==1){
            t = fj[0];
        }
        else{
            t = x-fj[0];
        }
        for(int j = 1;j<n;j++){
            if(binary[i][j]==1){
                t=t*fj[j];
            }
            else{
                t=t*(x-fj[j]);
            }
        }
        fjij[i] = t;
        //cout<<t<<endl;
    }
    std::vector<ECPoint> cdk2(n);
    std::vector<ECPoint> cdk1(n);
    std::vector<ECPoint> cdk3(n);
    std::vector<ECPoint> C2(m+1);
    for(int i = 0;i<m;i++){
        C2[i] = Y-upk[i];
    }
    for(int i = 0;i<n;i++){
        ECPoint t = T*Pi[0][i];
        ECPoint t1 = upk[0]*Pi[0][i];
        ECPoint t2 = C2[0]*Pi[0][i];
        for(int j = 1;j<m;j++){
            t+=T*Pi[j][i];
            t1+=upk[j]*Pi[j][i];
            t2+=C2[j]*Pi[j][i];
        }
        t +=ecp_E*rouks[i];
        t1 +=com_pp.g*rouks[i];
        t2+=C2[m]*rouks[i];
        cdk3[i] = t2;
        cdk2[i] = t;
        cdk1[i] = t1;
    }
    C2[m] = pk_recover;
    for(int i = 0;i<n;i++){
        zuo1[i] = Pederson_commitments_lj[i]*x+Pederson_commitments_aj[i];
        you1[i] = com_pp.g*zaj[i]+com_pp.g*2*fj[i];
        bool equal = zuo1[i].CompareTo(you1[i]);
        if(equal==false){
             std::cout << "verify fail"<<std::endl; 
        }
    }
    //cout<<"length:"<<len0+len<<endl;
    cout << "签名验证通过,相关信息展示（链接标志T、监管信息C、环签名）" << endl;
        auto end1 = std::chrono::steady_clock::now();
        std::cout << "签名验证时间"
              << ":" << std::chrono::duration<double, std::milli>(end1 - start1).count() << " ms" << std::endl;
}
string GetBinaryStringFromHexString (string strHex)
{
    string sReturn = "";
    unsigned int len = strHex.length();
    for (unsigned int i = 0; i<len; i++)
    {
        switch ( strHex[i])
        {
            case '0': sReturn.append ("0000"); break;
            case '1': sReturn.append ("0001"); break;
            case '2': sReturn.append ("0010"); break;
            case '3': sReturn.append ("0011"); break;
            case '4': sReturn.append ("0100"); break;
            case '5': sReturn.append ("0101"); break;
            case '6': sReturn.append ("0110"); break;
            case '7': sReturn.append ("0111"); break;
            case '8': sReturn.append ("1000"); break;
            case '9': sReturn.append ("1001"); break;
            case 'A': sReturn.append ("1010"); break;
            case 'B': sReturn.append ("1011"); break;
            case 'C': sReturn.append ("1100"); break;
            case 'D': sReturn.append ("1101"); break;
            case 'E': sReturn.append ("1110"); break;
            case 'F': sReturn.append ("1111"); break;
        }
    }
    return sReturn;
}

//Pedersen Commitment
ECPoint Commit(PP &pp,  std::vector<BigInt>& vec_m, BigInt r)
{
    if(pp.N_max < vec_m.size()){
        std::cerr << "message size is less than pp size" << std::endl;
    }
    size_t LEN = vec_m.size();
    std::vector<ECPoint> subvec_h(pp.vec_h.begin(), pp.vec_h.begin() + LEN);
    ECPoint commitment = pp.g * r + ECPointVectorMul(subvec_h, vec_m);
    return commitment;   
}



void file()
{
    char data[2];
 
   // 以写模式打开文件
   ofstream outfile;
   outfile.open("file.txt");
 
   cout << "Writing to the file" << endl;
   cout << "Enter your name: "; 
   cin.getline(data, 2);
 
   // 向文件写入用户输入的数据
   outfile << data << endl;
 
   cout << "Enter your age: "; 
   cin >> data;
   cin.ignore();
   
   // 再次向文件写入用户输入的数据
   outfile << data << endl;
 
   // 关闭打开的文件
   outfile.close();
 
   // 以读模式打开文件
   ifstream infile; 
   infile.open("afile.dat"); 
 
   cout << "Reading from the file" << endl; 
   infile >> data; 
 
   // 在屏幕上写入数据
   cout << data << endl;
   
   // 再次从文件读取数据，并显示它
   infile >> data; 
   cout << data << endl; 
 
   // 关闭打开的文件
   infile.close();
 

}

void System()
{
std::cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++" << std::endl; 
std::cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++" << std::endl; 
std::cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++" << std::endl; 
std::cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++" << std::endl;
std::cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++" << std::endl; 
std::cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++" << std::endl; 
std::cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++" << std::endl; 
std::cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++" << std::endl; 
std::cout << "+++|欢迎来到基于 DID 的可授权可验证隐私数据医疗共享系统|+++++" << std::endl; 
std::cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++ " << std::endl; 
std::cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++" << std::endl; 
std::cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++" << std::endl; 
std::cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++" << std::endl; 
std::cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++" << std::endl; 
std::cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++" << std::endl; 
std::cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++" << std::endl; 
std::cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++" << std::endl;
while (1)
{
std::cout << "请选择您的身份:" << std::endl; 
std::cout << "1.患者A " << std::endl; 
std::cout << "2.医院B" << std::endl; 
std::cout << "3.主治医生D（工作单位为医院E）" << std::endl; 
std::cout << "4.医生C（工作单位为医院B）" << std::endl; 
std::cout << "5.监管机构" << std::endl; 
std::cout << "6.医院E" << std::endl; 
std::cout << "你的输入为：" << std::endl; 
std::string input;
std::getline(std::cin, input);
PrintSplitLine('-'); 

while (input=="1")
{
std::cout << "请选择您的操作：" << std::endl; 
PrintSplitLine('-'); 
std::cout << "1.在医院E注册 " << std::endl; 
std::cout << "2.在医院B注册" << std::endl; 
std::cout << "3.看病" << std::endl; 
std::cout << "0.退出" << std::endl; 
PrintSplitLine('-'); 

std::string input1;
std::cout << "你的输入为：" << std::endl; 
std::getline(std::cin, input1);
if (input1=="0")
{
break;
}
if (input1=="1")
{
std::string input3;
std::cout << "请输入您的身份证号:" << std::endl; 
std::getline(std::cin, input3);
PrintSplitLine('-'); 
std::cout << "正在为您注册-" << std::endl; 
PrintSplitLine('-'); 
std::cout << "注册完成，您的DID为：xxxxx" << std::endl; 
PrintSplitLine('-'); 
std::cout << "DID文档已上链" << std::endl; 


 char data[10000];
 ifstream infile; 
 infile.open("DID Document.txt"); 
 

 cout << "在链上读取最新的DID文档" << endl; 
 infile >> data; 
 
// 再次从文件读取数据，并显示它
 infile >> data; 
 cout << data << endl; 
 
// 关闭打开的文件
  infile.close();



}
if (input1=="2")
{
std::string input4;
std::cout << "请输入您的身份证号:" << std::endl; 
std::getline(std::cin, input4);
PrintSplitLine('-'); 
std::cout << "正在为您注册" << std::endl; 
PrintSplitLine('-'); 
std::cout << "注册完成，您的DID为：xxxxx" << std::endl; 
std::cout << "DID文档已上链" << std::endl; 

char data[10000];
 ifstream infile; 
 infile.open("DID Document.txt"); 
 

 cout << "在链上读取最新的DID文档" << endl; 
 infile >> data; 
 
// 再次从文件读取数据，并显示它
 infile >> data; 
 cout << data << endl; 
 
// 关闭打开的文件
  infile.close();

    std::cout << "是否允许使用您的数据？" << std::endl; 
    PrintSplitLine('-'); 
    std::cout << "0.退出" << std::endl; 
    std::cout << "1.是" << std::endl; 
    std::cout << "2.否" << std::endl; 
    std::cout << "你的输入为：" << std::endl; 
    std::string input8;
    std::getline(std::cin, input8);
    PrintSplitLine('-'); 
if (input8=="0")
{
break;
}
if (input8=="1")
{
std::cout << "授权成功，医院B可以计算您的数据，生成UID" << std::endl; 
PrintSplitLine('-'); 
std::cout << "EAP" << std::endl; 

}
if (input8=="2")
{
PrintSplitLine('-'); 
std::cout << "系统结束" << std::endl;
PrintSplitLine('-'); 
break;
}
}

if (input1=="3")
{
std::string input5;
std::cout << "请选择您想去的医院:"<< std::endl; 
std::cout << "1.在医院B" << std::endl; 
std::cout << "2.在医院E" << std::endl; 
std::cout << "0.退出" << std::endl; 
std::cout << "你的输入为：" << std::endl; 
PrintSplitLine('-'); 
std::getline(std::cin, input5);
PrintSplitLine('-'); 
if (input5=="0")
{
break;
}
if (input5=="1")
{
    string input23;
    std::cout << "请输入混淆程度："<< std::endl; 
    std::cout << "1.8个混淆成员" << std::endl; 
std::cout << "2.16个混淆成员" << std::endl; 
std::cout << "3.64个混淆成员" << std::endl; 
std::cout << "你的输入为：" << std::endl; 
PrintSplitLine('-'); 
std::getline(std::cin, input23);
PrintSplitLine('-'); 
char data[10000];
 ifstream infile; 
 infile.open("medicalrecord.txt"); 

PrintSplitLine('-'); 
PrintSplitLine('-'); 
std::cout << "病历生成完毕,医生对病历进行签名" << std::endl; 
functionring();
cout << "相关信息展示（链接标志T、监管信息C、环签名）" << endl;
infile >> data; 
 
// 再次从文件读取数据，并显示它
 infile >> data; 
 cout << data << endl; 
// 关闭打开的文件
  infile.close();
PrintSplitLine('-'); 
}
if (input5=="2")
{
std::cout << "是否需要调用您之前的病历？" << std::endl; 
PrintSplitLine('-'); 
std::cout << "0.退出" << std::endl; 
std::cout << "1.需要" << std::endl; 
std::cout << "2.不需要" << std::endl; 
PrintSplitLine('-'); 
std::cout << "你的输入为：" << std::endl; 
std::string input6;
std::getline(std::cin, input6);
PrintSplitLine('-'); 
if (input6=="0")
{
break;
}
if (input6=="1")
{
    std::cout << "是否进行查询授权？" << std::endl; 
    PrintSplitLine('-'); 
    std::cout << "0.退出" << std::endl; 
    std::cout << "1.需要" << std::endl; 
    std::cout << "2.不需要" << std::endl; 
    std::cout << "你的输入为：" << std::endl; 
    std::string input7;
    std::getline(std::cin, input7);
    PrintSplitLine('-'); 
if (input7=="0")
{
break;
}
if (input7=="1")
{
std::cout << "授权成功，主治医生D可进行查询" << std::endl; 
PrintSplitLine('-'); 
std::cout << "证明信息（DID,UIDs,Tokens and Proofs）上链" << std::endl; 

char data[10000];
 ifstream infile; 
 infile.open("Proof.txt"); 
 cout << "在链上读取最新的证明信息" << endl; 
 infile >> data; 
 
// 再次从文件读取数据，并显示它
 infile >> data; 
 cout << data << endl; 
 
// 关闭打开的文件
  infile.close();


PrintSplitLine('-'); 
std::cout << "医院B验证授权成功" << std::endl; 
PrintSplitLine('-'); 
std::cout << "开始批量查询" << std::endl; 



std::cout << "System Setup begins >>>" << std::endl; 
    CRYPTO_Initialize(); 
   // ECPoint G = ECPoint(generator); 
    //ECPoint H = GenRandomECPoint(); 
    //std::cout<<G.CompareTo(H)<<std::endl;


    PrintSplitLine('-');  
    std::cout << "generate or load public parameters and test case" << std::endl;

    // generate pp (must be same for both server and client)
    std::string pp_filename = "mqRPMTPSI.pp"; 
    mqRPMTPSI::PP pp;   
    if(!FileExist(pp_filename)){
        std::cout << pp_filename << " does not exist" << std::endl; 
        std::string filter_type = "bloom"; 
        size_t computational_security_parameter = 128;         
        size_t statistical_security_parameter = 40; 
        size_t LOG_SENDER_LEN = 20;
        size_t LOG_RECEIVER_LEN = 8;  
        pp = mqRPMTPSI::Setup("bloom", computational_security_parameter, statistical_security_parameter, 
                              LOG_SENDER_LEN, LOG_RECEIVER_LEN); 
        mqRPMTPSI::SavePP(pp, pp_filename); 
    }
    else{
        std::cout << pp_filename << " already exists" << std::endl; 
        mqRPMTPSI::FetchPP(pp, pp_filename); 
    }

    std::string testcase_filename = "mqRPMTPSI.testcase"; 
    
    // generate test instance (must be same for server and client)
    TestCase testcase; 
    if(!FileExist(testcase_filename)){ 
        std::cout << testcase_filename << " does not exist" << std::endl; 
        testcase = GenTestCase(pp.LOG_SENDER_LEN, pp.LOG_RECEIVER_LEN); 
        SaveTestCase(testcase, testcase_filename); 
    }
    else{
        std::cout << testcase_filename << " already exist" << std::endl; 
        FetchTestCase(testcase, testcase_filename);
        if((testcase.LOG_SENDER_LEN != pp.LOG_SENDER_LEN) || (testcase.LOG_SENDER_LEN != pp.LOG_SENDER_LEN)){
            std::cerr << "testcase and public parameter do not match" << std::endl; 
        }
    }
   std::cout << "mqRPMT-based PSI test begins >>>" << std::endl; 
    PrintTestCase(testcase); 

    std::string party;

    std::cout << "please select your role between sender and receiver (hint: first start receiver, then start sender) ==> "; 

    std::getline(std::cin, party);
    PrintSplitLine('-'); 
// PSI-Payload Protocol
    if(party == "sender"){
        NetIO client("client", "127.0.0.1", 8080);  
       // mqRPMTPSI::Send_UID(client,pp,UID);
        mqRPMTPSI::Send(client, pp, testcase.vec_X,testcase.vec_D,UID);
      
    } 

    if(party == "receiver"){
        NetIO server("server", "127.0.0.1", 8080);
        mqRPMTPSI::Send_Token(server,pp,Token);
        std::vector<block> vec_intersection_prime = mqRPMTPSI::Receive(server, pp, testcase.vec_Y,sk_c);
        std::set<block, BlockCompare> set_diff_result = 
            ComputeSetDifference(vec_intersection_prime, testcase.vec_intersection);  

        double error_probability = set_diff_result.size()/double(testcase.vec_intersection.size()); 
        std::cout << "mqRPMT-based PSI test succeeds with probability " << (1 - error_probability) << std::endl; 
    }

    CRYPTO_Finalize();   



std::cout << "查询成功" << std::endl;
PrintSplitLine('-'); 
}
if (input7=="2")
{
PrintSplitLine('-'); 
std::cout << "系统结束" << std::endl;
PrintSplitLine('-'); 
break;
}
}
if (input6=="2")
{
    PrintSplitLine('-'); 
    std::cout << "系统结束" << std::endl;
    PrintSplitLine('-'); 
    break;
}
}
}
}

PrintSplitLine('-'); 
while (input=="2")
{
     std::cout << "System Setup begins >>>" << std::endl; 
    CRYPTO_Initialize(); 
   // ECPoint G = ECPoint(generator); 
    //ECPoint H = GenRandomECPoint(); 
    //std::cout<<G.CompareTo(H)<<std::endl;


    PrintSplitLine('-');  
    std::cout << "generate or load public parameters and test case" << std::endl;

    // generate pp (must be same for both server and client)
    std::string pp_filename = "mqRPMTPSI.pp"; 
    mqRPMTPSI::PP pp;   
    if(!FileExist(pp_filename)){
        std::cout << pp_filename << " does not exist" << std::endl; 
        std::string filter_type = "bloom"; 
        size_t computational_security_parameter = 128;         
        size_t statistical_security_parameter = 40; 
        size_t LOG_SENDER_LEN = 20;
        size_t LOG_RECEIVER_LEN = 8;  
        pp = mqRPMTPSI::Setup("bloom", computational_security_parameter, statistical_security_parameter, 
                              LOG_SENDER_LEN, LOG_RECEIVER_LEN); 
        mqRPMTPSI::SavePP(pp, pp_filename); 
    }
    else{
        std::cout << pp_filename << " already exists" << std::endl; 
        mqRPMTPSI::FetchPP(pp, pp_filename); 
    }

    std::string testcase_filename = "mqRPMTPSI.testcase"; 
    
    // generate test instance (must be same for server and client)
    TestCase testcase; 
    if(!FileExist(testcase_filename)){ 
        std::cout << testcase_filename << " does not exist" << std::endl; 
        testcase = GenTestCase(pp.LOG_SENDER_LEN, pp.LOG_RECEIVER_LEN); 
        SaveTestCase(testcase, testcase_filename); 
    }
    else{
        std::cout << testcase_filename << " already exist" << std::endl; 
        FetchTestCase(testcase, testcase_filename);
        if((testcase.LOG_SENDER_LEN != pp.LOG_SENDER_LEN) || (testcase.LOG_SENDER_LEN != pp.LOG_SENDER_LEN)){
            std::cerr << "testcase and public parameter do not match" << std::endl; 
        }
    }
   std::cout << "mqRPMT-based PSI test begins >>>" << std::endl; 
    PrintTestCase(testcase); 

    std::string party;

    std::cout << "please select your role between sender and receiver (hint: first start receiver, then start sender) ==> "; 

    std::getline(std::cin, party);
    PrintSplitLine('-'); 
// PSI-Payload Protocol
    if(party == "sender"){
        NetIO client("client", "127.0.0.1", 8080);  
       // mqRPMTPSI::Send_UID(client,pp,UID);
        mqRPMTPSI::Send(client, pp, testcase.vec_X,testcase.vec_D,UID);
      
    } 

    if(party == "receiver"){
        NetIO server("server", "127.0.0.1", 8080);
        mqRPMTPSI::Send_Token(server,pp,Token);
        std::vector<block> vec_intersection_prime = mqRPMTPSI::Receive(server, pp, testcase.vec_Y,sk_c);
        std::set<block, BlockCompare> set_diff_result = 
            ComputeSetDifference(vec_intersection_prime, testcase.vec_intersection);  

        double error_probability = set_diff_result.size()/double(testcase.vec_intersection.size()); 
        std::cout << "mqRPMT-based PSI test succeeds with probability " << (1 - error_probability) << std::endl; 
    }
    CRYPTO_Finalize();   

}


PrintSplitLine('-'); 
while (input=="3")
{
    std::cout << "System Setup begins >>>" << std::endl; 
    CRYPTO_Initialize(); 
   // ECPoint G = ECPoint(generator); 
    //ECPoint H = GenRandomECPoint(); 
    //std::cout<<G.CompareTo(H)<<std::endl;


    PrintSplitLine('-');  
    std::cout << "generate or load public parameters and test case" << std::endl;

    // generate pp (must be same for both server and client)
    std::string pp_filename = "mqRPMTPSI.pp"; 
    mqRPMTPSI::PP pp;   
    if(!FileExist(pp_filename)){
        std::cout << pp_filename << " does not exist" << std::endl; 
        std::string filter_type = "bloom"; 
        size_t computational_security_parameter = 128;         
        size_t statistical_security_parameter = 40; 
        size_t LOG_SENDER_LEN = 20;
        size_t LOG_RECEIVER_LEN = 8;  
        pp = mqRPMTPSI::Setup("bloom", computational_security_parameter, statistical_security_parameter, 
                              LOG_SENDER_LEN, LOG_RECEIVER_LEN); 
        mqRPMTPSI::SavePP(pp, pp_filename); 
    }
    else{
        std::cout << pp_filename << " already exists" << std::endl; 
        mqRPMTPSI::FetchPP(pp, pp_filename); 
    }

    std::string testcase_filename = "mqRPMTPSI.testcase"; 
    
    // generate test instance (must be same for server and client)
    TestCase testcase; 
    if(!FileExist(testcase_filename)){ 
        std::cout << testcase_filename << " does not exist" << std::endl; 
        testcase = GenTestCase(pp.LOG_SENDER_LEN, pp.LOG_RECEIVER_LEN); 
        SaveTestCase(testcase, testcase_filename); 
    }
    else{
        std::cout << testcase_filename << " already exist" << std::endl; 
        FetchTestCase(testcase, testcase_filename);
        if((testcase.LOG_SENDER_LEN != pp.LOG_SENDER_LEN) || (testcase.LOG_SENDER_LEN != pp.LOG_SENDER_LEN)){
            std::cerr << "testcase and public parameter do not match" << std::endl; 
        }
    }
   std::cout << "mqRPMT-based PSI test begins >>>" << std::endl; 
    PrintTestCase(testcase); 

    std::string party;

    std::cout << "please select your role between sender and receiver (hint: first start receiver, then start sender) ==> "; 

    std::getline(std::cin, party);
    PrintSplitLine('-'); 
// PSI-Payload Protocol
    if(party == "sender"){
        NetIO client("client", "127.0.0.1", 8080);  
       // mqRPMTPSI::Send_UID(client,pp,UID);
        mqRPMTPSI::Send(client, pp, testcase.vec_X,testcase.vec_D,UID);
      
    } 

    if(party == "receiver"){
        NetIO server("server", "127.0.0.1", 8080);
        mqRPMTPSI::Send_Token(server,pp,Token);
        std::vector<block> vec_intersection_prime = mqRPMTPSI::Receive(server, pp, testcase.vec_Y,sk_c);
        std::set<block, BlockCompare> set_diff_result = 
            ComputeSetDifference(vec_intersection_prime, testcase.vec_intersection);  

        double error_probability = set_diff_result.size()/double(testcase.vec_intersection.size()); 
        std::cout << "mqRPMT-based PSI test succeeds with probability " << (1 - error_probability) << std::endl; 
    }
    CRYPTO_Finalize();   
}











PrintSplitLine('-'); 

while (input=="4")
{
PrintSplitLine('-'); 
std::cout << "正在为您在本医院注册-" << std::endl; 
PrintSplitLine('-'); 
std::cout << "注册完成，您的DID是：did:LRRS:04C9295D49F1647688A56E333596266EBA387DC33EAE6E6674BF2D9130B73525CB70B71136E0A4A487765DEE8C5CD079506AAA5FE61B54E16D61CBAEE6C5879075" << std::endl; 
PrintSplitLine('-'); 
std::cout << "DID文档已上链" << std::endl; 
 char data[10000];
 ifstream infile; 
 infile.open("DID Document2.txt"); 
 

 cout << "在链上读取最新的DID文档" << endl; 
 infile >> data; 
 
// 再次从文件读取数据，并显示它
 infile >> data; 
 cout << data << endl; 
 
// 关闭打开的文件
  infile.close();
  break;
} 

PrintSplitLine('-'); 


while (input=="5")

{
   std::cout << "现有病历列表" << std::endl; 
PrintSplitLine('-'); 
std::cout << "病历1-创建时间:2023/12/18 20:05" << std::endl; 
PrintSplitLine('-'); 
std::cout << "病历2-创建时间:2023/12/18 22:45" << std::endl; 
PrintSplitLine('-'); 
std::cout << "请选择需要恢复医生身份的病历（请输入序号）：" << std::endl; 
PrintSplitLine('-'); 
std::string input9;
std::getline(std::cin, input9);
PrintSplitLine('-'); 
if (input9=="2")
{
PrintSplitLine('-'); 
std::cout << "正在为您恢复医生身份" << std::endl;
PrintSplitLine('-'); 
std::cout << "恢复的医生身份：did:LRRS:04C9295D49F1647688A56E333596266EBA387DC33EAE6E6674BF2D9130B73525CB70B71136E0A4A487765DEE8C5CD079506AAA5FE61B54E16D61CBAEE6C5879075" << std::endl;
  PrintSplitLine('-'); 
    std::cout << "系统结束" << std::endl;
}
break;
} 


}
}*/

void test_schnorr(size_t TEST_NUM)
{
    std::cout << "begin the basic correctness test >>>" << std::endl; 
    
    Schnorr::PP pp = Schnorr::Setup(); 
    std::vector<ECPoint> pk(TEST_NUM); 
    std::vector<BigInt> sk(TEST_NUM);

    auto start_time = std::chrono::steady_clock::now(); 
    for(auto i = 0; i < TEST_NUM; i++){
        std::tie(pk[i], sk[i]) = Schnorr::KeyGen(pp); 
    }
    auto end_time = std::chrono::steady_clock::now(); 
    
    auto running_time = end_time - start_time;
    std::cout << "key generation takes time = " 
    << std::chrono::duration <double, std::milli> (running_time).count()/TEST_NUM << " ms" << std::endl;

    std::vector<Schnorr::SIG> sigma(TEST_NUM); 
    
    std::string message = "crypto is hard";  

    start_time = std::chrono::steady_clock::now(); 
    
    for(auto i = 0; i < TEST_NUM; i++){
        sigma[i] = Schnorr::Sign(pp, sk[i], message);
    }
    end_time = std::chrono::steady_clock::now(); 
    running_time = end_time - start_time;
    std::cout << "sign message takes time = " 
    << std::chrono::duration <double, std::milli> (running_time).count()/TEST_NUM << " ms" << std::endl;


    start_time = std::chrono::steady_clock::now(); 
    for(auto i = 0; i < TEST_NUM; i++){
        if(Schnorr::Verify(pp, pk[i], message, sigma[i]) == false){
            std::cout << "the " << i << "th verification fails" << std::endl;
        }
    }
    end_time = std::chrono::steady_clock::now(); 
    running_time = end_time - start_time;
    std::cout << "verify signature takes time = " 
    << std::chrono::duration <double, std::milli> (running_time).count()/TEST_NUM << " ms" << std::endl;
}



/*BigInt modular(int a,int n,int p)
{
     int n, a, p;
    int nn[30], aa[30], bb[30];
    int temp, num, r;
    int i = 0;
    temp = n;
    while (temp != 0) {
        num = temp % 2;
        nn[i] = num;
        i++;
        temp = temp / 2;
    }
    r = i - 1;
    aa[0] = a;
    bb[0] = a;
    for (i = 0; i < n; i++) {
        aa[i + 1] = (aa[i] * aa[i]) % p;
        bb[i + 1] = aa[i + 1];
    }
    int x;
    x = 1;
    for (i = 0; i <= r; i++) {
        if (nn[i] == 1) x = (x * bb[i]) % p;
    }
    cout << "the result is :";
    return x;


}*/

typedef unsigned long long ll;



ll qpow(ll r, ll n, ll mod){//计算a^n % mod
    ll re = 1;
    while(n){
        if(n & 1)
            re = (re * r) % mod;
        n >>= 1;
        r = (r * r) % mod;
    }
    return re % mod;
}

ll lpow(ll r, ll n ){//计算a^n
    ll re = 1;
    while(n){
        if(n & 1)
            re = (re * r);
        n >>= 1;
        r = (r * r);
    }
    return re;
}

ll byy(ll lp){//求Zlp*的本原元
    bool flag;
    for(ll i=2;i<lp;i++){
        flag=true;
        for(ll j=2;j<lp-1;j++){
            if((lp-1)%j==0){
                if(qpow(i,j,lp)==1) flag=false;
            }
        }
        if(flag) return i;
    }
}

ll inv(ll la, ll lp){//求逆元——扩展欧几里得算法
    if(la == 1) return 1;
    return inv(lp%la,lp)*(lp-lp/la)%lp;
}

void  SPIR(ll la,ll lp,ll ly,ll lr,string ID,string message,ll lx){
    unsigned long long c11;
    unsigned long long c22;
    unsigned long long m;
    unsigned long long message_long;
    //message_long=std::stoll(message);
    //message_long= 9859348590348;
    
    unsigned long long ID_long;
    ID_long=atoll(ID.c_str());

    message_long=atoll(message.c_str());

     std::cout << "ID"<<ID << std::endl;
    //ID_long= strtoll(ID.c_str(), NULL, 10);
    std::cout << "ID_long"<<ID_long << std::endl;
    std::cout << "message_long"<<message_long << std::endl;
    unsigned long long ID_long_v;
    ID_long_v=ID_long;
    //td::cout << "la"<<la << std::endl;
    printf("\n======加密======\n");
    unsigned long long lc=(rand()%(lp-0));
    unsigned long long ID_long_l_c_l_r=ID_long*lc*lr;
    c11=qpow(la,ID_long_l_c_l_r,lp);
    //unsigned long long i=0.5;
    c22=((message_long)*qpow(ly,ID_long_l_c_l_r,lp)*qpow(la,(ID_long_v-ID_long)*lc,lp))%lp;
    //std::cout << "qpow(ly,c55,lp)"<<qpow(ly,ID_long_l_c_l_r,lp) <<std::endl;
    std::cout << "密文c1-----------"<<c11 << "----------c22-------" <<c22<<std::endl;
    std::cout << "message_long"<<message_long%lp << std::endl;


    printf("\n======解密======\n");
    unsigned long long c33=qpow(c11,lx,lp);
    std::cout << "c33-----------"<<c33 <<std::endl;
    unsigned long long c44=inv(c33,lp);
    std::cout << "c44-----------"<<c44 <<std::endl;
    m=(c22*c44)%lp;
    std::cout << "m---------"<<m<<std::endl;
    if(m==message_long%lp)
    {
        printf("\n======解密成功======\n");
    }

}







/*void ASPIR()
{


    std::cout << " Brands-RSA Credential Issuing protocol" << std::endl;

    unsigned long long A,Y;
    printf("请输入参数p并随机选取密钥x(0<x<p-1):");
    ll p=1095791; //p = 1031 q = 1061
    ll x=4;
    A=byy(p);
    Y=qpow(A,x,p);
    printf("计算出本原元a=%lld   公钥y=%lld\n",A,Y);
    printf("请输入要加密的明文m(m=Zp*)：");
    std::string message = "328492308";  
    printf("请输入随机产生的参数r(r=Zp*,gcd(r,p-1)=1):");
    ll r=673;
   // encode(a,p,y,r);  //加密
   //decode(x,p);  //解密

    unsigned long long l=40;
    unsigned long long v=323;
    unsigned long long  g[50];
    unsigned long long  y1[50];
    unsigned long long  g_y[50];
    unsigned long long  x_0;
    unsigned long long  h;

//h0
    x_0=rand()%(p);
    unsigned long long h_0=qpow(x_0, v, p);
      std::cout << " h_0" << h_0<< std::endl;

//h=g1^x1 * g2^x2 * gl^xl
    for(int i=0;i<l;i++)
    {
      y1[i]=(rand()%(v-0));
      g[i]=(rand()%(p-0));
      g_y[i]=qpow(g[i],y1[i], p);
      h=h*g_y[i]%p;
    }
std::cout << " h" << h<< std::endl;

//a1^v
   unsigned long long a_1=(rand()%(p-0));
    unsigned long long a_1_v=qpow(a_1, v, p);

//h'
 unsigned  long long h_2;
  h_2=h*a_1_v%p;
std::cout << " h_2" << h_2<< std::endl;
//h*h0
 unsigned  long long h_0_h_1;
    h_0_h_1 =h*h_0%p;
std::cout << " h_0_h_1" << h_0_h_1<< std::endl;

//(h*h0)^a3*a0*a2^v
unsigned long long a_0=360;
unsigned long long a_2=(rand()%(p-0));
unsigned long long a_2_v=qpow(a_1, v, p);
unsigned long long a_3=(rand()%(p-0));
//h3
unsigned long long h_3=(qpow(h_0_h_1,a_3, p)*a_2_v*a_0)%p+h_2;
std::cout << " h_3" << h_3<< std::endl;


// h3_str
std::string h3_str = std::to_string(h_3);
std::cout << " h3_str" << h3_str<< std::endl;
//c0
string c_0;
c_0=sha256(h3_str);
std::cout << " c_0" << c_0<< std::endl;
//c1
double  c_1=(h_3+a_3)%7;
std::cout << " c_1" << c_1<< std::endl;
//r0
//a_0=360;
//unsigned long long r_0_0=qpow(h_0_h_1,c_1, p);
double r_0_0=pow(h_0_h_1%9,double(c_1));
//unsigned long long r_0_1=(r_0_0*a_0)%p;
double r_0_1=(r_0_0*(a_0));
std::cout << "r_0_1" <<r_0_1<< std::endl;


//unsigned long long r_11=qpow(r_0_1,v, p);
double r_0=pow(r_0_1,double(0.5));
//unsigned long long r_0=inv(r_11,p);
//unsigned long long r_0=inv(r_11,2);
std::cout << " r_0" << r_0<< std::endl;

//a0==aa4
double  a_6;
//a_6=qpow(r_0,v,p);
a_6=(r_0_0*(a_0));
std::cout << "a_6" <<a_6<< std::endl;

//unsigned long long a_7=inv(r_0_0,p);
double a_7=1/r_0_0;
std::cout << "a_7" <<a_7<< std::endl;
double  a_4;
//a_4=(a_6*a_7)%p;
a_4=(a_6*a_7);

std::cout << "a_4" << a_4<< std::endl;
if(a_4==a_0)
{
    std::cout << "a_4==a_0" << std::endl;

}else{
    std::cout << "a_4!=a_0" <<a_0/3<< std::endl;
     std::cout << "inv(qpow(h_0_h_1,c_1,p),p)" <<inv(qpow(h_0_h_1,c_1,p),p)<< std::endl;
      std::cout << "qpow(r_0,v,p)" <<qpow(r_0,v,p)<< std::endl;
}

//r1
unsigned long long r_1;
r_1=r_0*a_2*qpow(a_1, c_1, p)*qpow(h_0_h_1, c_1, p);

 std::cout << " Aut Proof (c_0, r1)" << std::endl;





std::cout << "Brands-RSA basic Credential Showing protocol" << std::endl;


//w1,....wl
   long long  w[50];
    for(int i=0;i<l;i++)
    {
      w[i]=(rand()%(v-0));

    }
    w[l+1]=(rand()%(p-0));

//a
     long long  a;
    for(int i=0;i<l;i++)
    {
      a=a*qpow(g[i],w[i], p);

    }

    a=a*qpow(w[l+1],v, p);
   std::string a_str = std::to_string(a);
    

//c
string c_2;
c_2=sha256(a_str+message);
long long c_2_long;
c_2_long= strtoll(c_2.c_str(), NULL, 10);

//t1......tl
long long t[50];
long long g_t;
for(int i=0;i<l;i++)
    {
      t[i]=(c_2_long*y1[i]%v+w[i]);
      g_t=g_t*(qpow(g[i],t[i], p));
    }




//rl+1
 long long r_l_1;
 r_l_1=g_t*qpow(x_0,c_2_long, p)*w[l+1];

   

//verify Aut Proof
//c_0'
 long long c_0_verf;

c_0_verf=qpow(r_1,v, p)*(1/qpow(h_0*h_2,h_3, p))+h_3;

// h3_str
std::string c_0_verf_str = std::to_string(c_0_verf);

//c0
string c_0_verf_str_hash;
c_0_verf_str_hash=sha256(c_0_verf_str);

if(c_0_verf_str_hash==c_0)
{
    std::cout << "c_0_verf_str_hash==c_0" << std::endl;

}

else{
     std::cout << "c_0_verf_str_hash!=c_0" << std::endl;
}

string c_3;
c_3=sha256(a_str+message);

if(c_3==c_2)
{
    std::cout << "c_3==c_2" << std::endl;

}else
{
    std::cout << "c_3!=c_2" << std::endl;

}

//a'
long long a_verfy;
a_verfy=g_t*qpow(r_l_1,v, p)*(1/qpow(h_2,c_2_long, p));
if (a==a_verfy)
{
     std::cout << "a==a" << std::endl;
}else
{
    std::cout << "a!=a" << std::endl;

}
string ID="5839584";
SPIR(A,p,Y,r,ID,message,x);  //加密


 

}*/



int main()
{
auto start_time4 = std::chrono::steady_clock::now(); 
ASPIR();
//System();
auto end_time_4 = std::chrono::steady_clock::now(); 
auto running_time_4 = end_time_4- start_time4;
 std::cout << "ASPIR takes time = " 
              << std::chrono::duration <double, std::milli> (running_time_4).count() << " ms" << std::endl;

std::cout << "System Setup begins >>>" << std::endl; 
    CRYPTO_Initialize(); 
   // ECPoint G = ECPoint(generator); 
    //ECPoint H = GenRandomECPoint(); 
    //std::cout<<G.CompareTo(H)<<std::endl;


    PrintSplitLine('-');  
    std::cout << "generate or load public parameters and test case" << std::endl;

    // generate pp (must be same for both server and client)
    std::string pp_filename = "mqRPMTPSI.pp"; 
    mqRPMTPSI::PP pp;   
    if(!FileExist(pp_filename)){
        std::cout << pp_filename << " does not exist" << std::endl; 
        std::string filter_type = "bloom"; 
        size_t computational_security_parameter = 128;         
        size_t statistical_security_parameter = 40; 
        size_t LOG_SENDER_LEN = 12;
        size_t LOG_RECEIVER_LEN = 8;  
        pp = mqRPMTPSI::Setup("bloom", computational_security_parameter, statistical_security_parameter, 
                              LOG_SENDER_LEN, LOG_RECEIVER_LEN); 
        mqRPMTPSI::SavePP(pp, pp_filename); 
    }
    else{
        std::cout << pp_filename << " already exists" << std::endl; 
        mqRPMTPSI::FetchPP(pp, pp_filename); 
    }

    std::string testcase_filename = "mqRPMTPSI.testcase"; 
    
    // generate test instance (must be same for server and client)
    TestCase testcase; 
    if(!FileExist(testcase_filename)){ 
        std::cout << testcase_filename << " does not exist" << std::endl; 
        testcase = GenTestCase(pp.LOG_SENDER_LEN, pp.LOG_RECEIVER_LEN); 
        SaveTestCase(testcase, testcase_filename); 
    }
    else{
        std::cout << testcase_filename << " already exist" << std::endl; 
        FetchTestCase(testcase, testcase_filename);
        if((testcase.LOG_SENDER_LEN != pp.LOG_SENDER_LEN) || (testcase.LOG_SENDER_LEN != pp.LOG_SENDER_LEN)){
            std::cerr << "testcase and public parameter do not match" << std::endl; 
        }
    }
  auto start_time = std::chrono::steady_clock::now(); 
// sk Generate
 size_t DID_sk_len = testcase.vec_Y.size(); 
 std::vector<int> DID_sk(DID_sk_len);
 for (auto i = 0; i < testcase.RECEIVER_LEN; i++) {
        
        DID_sk[i]= rand(); 
        //std::cout << "DID_sk[0] >>>" <<DID_sk[0]<< std::endl; 
       // break;
    }
 
    std::vector<uint8_t> HID_randnum;
    size_t testcase_HID_LEN = testcase.vec_Y.size(); 
    std::vector<std::vector<uint8_t>> vec_YHID(testcase_HID_LEN,std::vector<uint8_t>(testcase_HID_LEN));
    std::vector<std::vector<uint8_t>> vec_XHID(testcase_HID_LEN,std::vector<uint8_t>(testcase_HID_LEN));
    //vector<string> vec_HID(testcase_HID_LEN);
    vector<string> vec_RHID(testcase_HID_LEN);
    vector<string> vec_RHID_hex(testcase_HID_LEN);
    vector<string> vec_HID_bit(testcase_HID_LEN);
    string vec_UID_bit_num="";
    std::vector<ECPoint> UID (testcase.RECEIVER_LEN);
    //UID Generate
   /*for (auto i = 0; i < testcase.RECEIVER_LEN; i++) {
          //std::cout<<"vec_HID[i].data()"<<std::endl;
          BasicHash((uint8_t*)(testcase.vec_Y.data()+i),sizeof(block), vec_HID[i].data());
          //std::cout<<"11111111"<<std::endl;
          //std::cout<<"vec_HID[i].data()"<<vec_HID[i].data()<<std::endl;
          int HID_random=rand();
          //HID_randnum[i]=rand(); 
          //std::cout<<"HID_randnum[i]"<<ii<<std::endl;
          //string d = multiply( HID_randnum[i],vec_HID[i].data());
          //uint8_t* char_array[d.length()];
          vec_UID[i]=multiply(std::to_string(HID_random),vec_HID[i].data());
          vec_UID_hex[i]=string_to_hex(vec_UID[i]);
          //std::cout<<"UID"<<multiply( HID_randnum[i],vec_HID[i].data())<<std::endl;
          //std::cout<<"UID"<<vec_UID_hex[0]<<std::endl;
         // break;
          vec_UID_bit[i]=GetBinaryStringFromHexString(vec_UID_hex[i]);
          vec_UID_bit_num=vec_UID_bit_num+vec_UID_bit[i];
    }*/
           //std::cout<<"ec_UID_bit_num"<<vec_UID_bit_num<<std::endl;
     string did="did:";
     string protocol="ASKPIR:";
     size_t N_max = testcase.RECEIVER_LEN; 
     PP com_pp = Setup(N_max); 
     std::vector<BigInt> BN_RHID(testcase.RECEIVER_LEN);
     std::vector<BigInt> BN_DID_sk(testcase.RECEIVER_LEN);
     std::vector<ECPoint> Pederson_commitment(testcase.RECEIVER_LEN);
     std::vector<string> Pederson_commitment_str(testcase.RECEIVER_LEN);
     std::vector<string> Pederson_commitment_hex(testcase_HID_LEN);
     std::vector<string> DID(testcase_HID_LEN);
     BigInt sk_c=GenRandomBigIntLessThan(order); 
     std::vector<ECPoint> pk_c (testcase.RECEIVER_LEN);
     std::vector<ECPoint> Token(testcase.RECEIVER_LEN);
     std::vector<string> Token_str(testcase.RECEIVER_LEN);
     std::vector<string> Token_hex(testcase_HID_LEN);
     std::vector<string> UID_hex(testcase_HID_LEN);
     std::vector<string> UID_str(testcase_HID_LEN);
     int HID_random[testcase.vec_Y.size()];
    vector<string> DID_bit(testcase_HID_LEN);
    string DID_double_num="";
    vector<string> Token_bit(testcase_HID_LEN);
    string Token_double_num="";
     //Generate DID UID 
     for (auto i = 0; i < testcase.RECEIVER_LEN; i++) {



//HID
 BasicHash((uint8_t*)(testcase.vec_Y.data()+i),sizeof(block), vec_YHID[i].data()); //H(Y)
 //BasicHash((uint8_t*)(testcase.vec_X.data()+i),sizeof(block), vec_XHID[i].data());
          //std::cout<<"11111111"<<std::endl;
          //std::cout<<"vec_HID[i].data()"<<vec_HID[i].data()<<std::endl;
          HID_random[i]=rand();
          //HID_randnum[i]=rand(); 
          //std::cout<<"HID_randnum[i]"<<ii<<std::endl;
          //string d = multiply( HID_randnum[i],vec_HID[i].data());
          //uint8_t* char_array[d.length()];
          vec_RHID[i]=multiply(std::to_string(HID_random[i]),vec_YHID[i].data());
          vec_RHID_hex[i]=string_to_hex(vec_RHID[i]);
          //std::cout<<"UID"<<multiply( HID_randnum[i],vec_HID[i].data())<<std::endl;
          //std::cout<<"UID"<<vec_UID_hex[0]<<std::endl;
         // break;
          vec_HID_bit[i]=GetBinaryStringFromHexString(vec_RHID_hex[i]);
          vec_UID_bit_num=vec_UID_bit_num+vec_HID_bit[i];


//DID
         BN_DID_sk[i]=Hash::StringToBigInt(std::to_string(DID_sk[i]));
         BN_RHID[i]=Hash::StringToBigInt(vec_RHID[i]);
         Pederson_commitment[i] = Commit(com_pp,BN_DID_sk,BN_DID_sk[i]);
         Pederson_commitment_str[i]="";
         Pederson_commitment_str[i]+=Pederson_commitment[i].ToByteString();
         Pederson_commitment_hex[i]=ToHexString(Pederson_commitment_str[i]);
         DID[i]=did+protocol+Pederson_commitment_hex[i];
       //std::cout<<"DID[i]"<<DID[0]<<std::endl;
//UID
         UID[i]=com_pp.g*Hash::StringToBigInt(vec_RHID[i]);
         UID_str[i]=Hash::ECPointToString(UID[i]);
         UID_hex[i]=ToHexString(UID_str[i]);


//Token
         pk_c[i]=com_pp.g*sk_c;
        //std::cout<<"SK_c"<<k_1.ToHexString()<<std::endl;
        //std::cout<<"PK_c"<<W[0].ToHexString()<<std::endl;
         Token[i]=pk_c[i]*BN_RHID[i];
         Token_str[i]="";
         Token_str[i]+=Token[i].ToByteString();
         Token_hex[i]=ToHexString(Token_str[i]);
        //std::cout<<"Token"<<u_hex[0]<<std::endl;
        //break;
        DID_bit[i]=GetBinaryStringFromHexString(DID[i]);
        DID_double_num=DID_double_num+DID_bit[i];

        Token_bit[i]=GetBinaryStringFromHexString(Token_hex[i]);
        Token_double_num=Token_double_num+Token_bit[i];




    } 
    //cout<<"zheli:"<<DID[1]<<endl;
    //std::cout<<"ec_UID_bit_num"<<DID_double_num<<std::endl;
    //std::cout<<"ec_UID_bit_num"<<u_double_num<<std::endl;

    
    //GenProof
     std::vector<BigInt> r_1(testcase.RECEIVER_LEN);
     std::vector<BigInt> r_2(testcase.RECEIVER_LEN);
     //std::vector<BigInt> length_1(testcase.SENDER_LEN+100);
     std::vector<BigInt> length(testcase.RECEIVER_LEN);
     std::vector<ECPoint> Q_1 (testcase.RECEIVER_LEN);
     std::vector<ECPoint> Q_2 (testcase.RECEIVER_LEN);
     std::vector<string> Q_1_str (testcase.RECEIVER_LEN);
     std::vector<string> Q_2_str (testcase.RECEIVER_LEN);
     std::vector<string> Q_3_str (testcase.RECEIVER_LEN);
     std::vector<BigInt> s_1(testcase.RECEIVER_LEN);
     std::vector<BigInt> s_2(testcase.SENDER_LEN);
     std::vector<BigInt> BN_c_1(testcase.RECEIVER_LEN);
     std::vector<string> s_1_str(testcase.RECEIVER_LEN);
     std::vector<string> s_2_str(testcase.RECEIVER_LEN);
     std::vector<string> BN_c_1_str(testcase.RECEIVER_LEN);
    std::vector<string> result1(testcase.RECEIVER_LEN);
     std::vector<string> result2(testcase.RECEIVER_LEN);
      //std::vector<string> str_c_1(testcase.SENDER_LEN+100);
    // size_t testcase_HID_LEN = testcase.vec_X.size(); 
     std::vector<std::vector<uint8_t>> vec_c_1(testcase_HID_LEN,std::vector<uint8_t>(testcase_HID_LEN));
    //std::vector<std::vector<string>> vec_c_1_str(testcase_HID_LEN,std::vector<string>(testcase_HID_LEN));
   // string vec_c_1_str[testcase.SENDER_LEN+100];
  
    vector<string> c_bit(testcase_HID_LEN);
   string c_double_num="";
    vector<string> s_1_bit(testcase_HID_LEN);
   string s_1_double_num="";
    vector<string> s_2_bit(testcase_HID_LEN);
    string s_2_double_num="";
   // std::vector<string> result1(testcase.RECEIVER_LEN+100);
   //Generate Authorization Proof
    for (auto i = 0; i < testcase.RECEIVER_LEN; i++) {
         r_1[i]=GenRandomBigIntLessThan(order); 
         r_2[i]=GenRandomBigIntLessThan(order); 
         Q_1[i]=com_pp.g*r_1[i]+com_pp.vec_h[i]*r_2[i];
        //std::cout<<"Hash::ECPointToString(Q_1[i])"<<Hash::ECPointToString(Q_1[i])<<std::endl;

        
         Q_2[i]=pk_c[i]*r_1[i];
        //std::cout<<"Hash::ECPointToString(Q_2[i])"<<Hash::ECPointToString(Q_2[i])<<std::endl;
         
         Q_1_str[i]+=Hash::ECPointToString(Q_1[i]);
         //std::cout<<"Q_1_str[i]"<<Q_1_str[i]<<std::endl;
         Q_2_str[i]+=Hash::ECPointToString(Q_2[i]);
        // std::cout<<"Q_2_str[i]"<<Q_2_str[i]<<std::endl;
         Q_3_str[i]=Q_1_str[i]+Q_2_str[i];

         length[i]=Q_3_str[i].length();

         //length_2[i]=Q_2_str[i].length();
      //  std::cout<<"Q_3_str[i]"<<Q_3_str[i]<<std::endl;
       // BasicHash((uint8_t*)((Q_3_str.data())+i),sizeof(length[i]), vec_c_1[i].data());
           result1[i]= sha256(Q_3_str[i]);
         //std::cout<<"vec_c_1[i].data()"<<vec_c_1[i].data()<<std::endl;
       // std::cout<<"vec_c_1[i].data()"<<vec_c_1[i].data()<<std::endl;
         // string vec_c_1_str="";
          string vec_c_1_str( (char*) vec_c_1[i].data());
          BN_c_1[i]=Hash::StringToBigInt(vec_c_1_str);
          //std::cout<<"vec_c_1_str"<<vec_c_1_str<<std::endl;
          s_1[i]=r_1[i]-BN_RHID[i]*BN_c_1[i];
          s_2[i]=r_2[i]-BN_DID_sk[i]*BN_c_1[i];
          s_1_str[i]=s_1[i].ToHexString();
          //std::cout<<"s_1_str[i]"<<s_1_str[i]<<std::endl;
          s_2_str[i]=s_2[i].ToHexString();
          //std::cout<<"s_2_str[i]"<<s_2_str[i]<<std::endl;
          BN_c_1_str[i]=BN_c_1[i].ToHexString();
          //std::cout<<"BN_c_1_str[i]"<<BN_c_1_str[i]<<std::endl;
         //vec_c_1_str=""; 
         // break;
    
        c_bit[i]=GetBinaryStringFromHexString(BN_c_1_str[i]);
        c_double_num=c_double_num+c_bit[i];

        s_1_bit[i]=GetBinaryStringFromHexString(s_1_str[i]);
        s_1_double_num=s_1_double_num+s_1_bit[i];

        s_2_bit[i]=GetBinaryStringFromHexString(s_2_str[i]);
        s_2_double_num=s_2_double_num+s_2_bit[i];
        

    }  
    auto end_time_1 = std::chrono::steady_clock::now(); 
    auto running_time_1 = end_time_1 - start_time;
    std::cout << "Gen Authorization takes time = " 
              << std::chrono::duration <double, std::milli> (running_time_1).count() << " ms" << std::endl;
    //std::cout<<"s_1_double_num"<<c_double_num.size()<<std::endl;
   // std::cout<<"s_2_double_num"<<s_2_double_num<<std::endl;
    std::cout << "DIDs,UIDs,Tokens and Proofs are uploaded to the Blockchain \\" << std::endl;
    std::cout << "DIDs" << " Such as:"<<DID[1]<<std::endl;
    std::cout << "UIDs" << " Such as:"<< UID_hex[1]<<std::endl;
    std::cout << "Tokens" << " Such as:"<< Token_hex[1]<<std::endl;
    std::cout << "Proof:(c,s_1,s_2)" << " Such as:("<< BN_c_1_str[1]<<","<<s_1_str[1]<<","<<s_2_str[1]<<")"<<std::endl;



     std::cout << "Communication Cost of Authorization" << " [" 
              << (c_double_num.size()+s_1_double_num.size()+s_2_double_num.size()+DID_double_num.size()+Token_double_num.size()+vec_UID_bit_num.size())<< " B]" << std::endl;  

   std::cout << "Communication Cost of Authorization" << " [" 
              <<fixed <<setprecision(10)<<double(c_double_num.size()+s_1_double_num.size()+s_2_double_num.size()+DID_double_num.size()+Token_double_num.size()+vec_UID_bit_num.size())/(1024*1024)<< " MB]" << std::endl; 
//Verify Authorization Proof
    std::vector<bool> vec_condition(testcase.RECEIVER_LEN, true);
     //std::vector<BigInt> length_1(testcase.SENDER_LEN+100);
     std::vector<BigInt> length_1(testcase.RECEIVER_LEN);
     std::vector<ECPoint> Q_4 (testcase.RECEIVER_LEN);
     std::vector<ECPoint> Q_5 (testcase.RECEIVER_LEN);
     std::vector<string> Q_4_str (testcase.RECEIVER_LEN);
     std::vector<string> Q_5_str (testcase.RECEIVER_LEN);
     std::vector<string> Q_6_str (testcase.RECEIVER_LEN);
     std::vector<BigInt> BN_c_2(testcase.RECEIVER_LEN);
     std::vector<string> BN_c_2_str(testcase.RECEIVER_LEN);
     //std::vector<string> result2(testcase.RECEIVER_LEN+100);
      //std::vector<string> str_c_1(testcase.SENDER_LEN+100);
    // size_t testcase_HID_LEN = testcase.vec_X.size(); 
     std::vector<std::vector<uint8_t>> vec_c_2(testcase_HID_LEN,std::vector<uint8_t>(testcase_HID_LEN));
    //std::vector<std::vector<string>> vec_c_1_str(testcase_HID_LEN,std::vector<string>(testcase_HID_LEN));
   // string vec_c_1_str[testcase.SENDER_LEN+100];
    for (auto i = 0; i < testcase.RECEIVER_LEN; i++) {
         Q_4[i]=(com_pp.g*BN_RHID[i]+com_pp.vec_h[i]*BN_DID_sk[i])*BN_c_1[i]+com_pp.g*s_1[i]+com_pp.vec_h[i]*s_2[i];
         //std::cout<<"Hash::ECPointToString(Q_4[i])"<<Hash::ECPointToString(Q_4[i])<<std::endl;
         Q_5[i]=Token[i]*BN_c_1[i]+pk_c[i]*s_1[i];
         //std::cout<<"Hash::ECPointToString(Q_5[i])"<<Hash::ECPointToString(Q_5[i])<<std::endl;

         Q_4_str[i]+=Hash::ECPointToString(Q_4[i]);
         // std::cout<<"Q_4_str[i]"<<Q_4_str[i]<<std::endl;
         Q_5_str[i]+=Hash::ECPointToString(Q_5[i]);
         // std::cout<<"Q_5_str[i]"<<Q_5_str[i]<<std::endl;
         Q_6_str[i]=Q_4_str[i]+Q_5_str[i];
        //std::cout<<"Q_6_str[i]"<<Q_6_str[1]<<std::endl;
         length_1[i]=Q_6_str[i].length();
         //length_2[i]=Q_2_str[i].length();
       //std::cout<<"Q_6_str[i]"<<Q_6_str[i]<<std::endl;

         BasicHash((uint8_t*)((Q_6_str.data())+i),sizeof(length_1[i]), vec_c_2[i].data());
         //std::cout<<"vec_c_1[i].data()"<<vec_c_2[i].data()<<std::endl;
         //std::cout<<"vec_c_2[i].data()"<<vec_c_1[i].data()<<std::endl;
          //string result2 = sha256(Q_6_str[i]);
          string vec_c_2_str( (char*) vec_c_2[i].data());
          BN_c_2[i]=Hash::StringToBigInt(vec_c_2_str);
          //std::cout<<"vec_c_2_str"<<vec_c_2_str<<std::endl;
         result2[i] = sha256(Q_6_str[i]);
         //std::cout<<"222222222222222222"<<result1[i] <<result2[i] <<std::endl;
           vec_condition[i] = (result1[i] == result2[i]); 
      // std::cout<<"vec_condition[i]"<<vec_condition[i]<<std::endl;
        
    }  

    auto end2_time = std::chrono::steady_clock::now(); 
    auto running_time2 = end2_time - end_time_1;
    std::cout << "Verify Authorization Proof takes time = " 
              << std::chrono::duration <double, std::milli> (running_time2).count() << " ms" << std::endl;
   




// SPIR
    std::cout << "mqRPMT-based PSI test begins >>>" << std::endl; 
    PrintTestCase(testcase); 

    std::string party;

    std::cout << "please select your role between sender and receiver (hint: first start receiver, then start sender) ==> "; 

    std::getline(std::cin, party);
    PrintSplitLine('-'); 
// PSI-Payload Protocol
    if(party == "sender"){
        NetIO client("client", "127.0.0.1", 8080);  
       // mqRPMTPSI::Send_UID(client,pp,UID);
        mqRPMTPSI::Send(client, pp, testcase.vec_X,testcase.vec_D,UID);
      
    } 

    if(party == "receiver"){
        NetIO server("server", "127.0.0.1", 8080);
        mqRPMTPSI::Send_Token(server,pp,Token);
        std::vector<block> vec_intersection_prime = mqRPMTPSI::Receive(server, pp, testcase.vec_Y,sk_c);
        std::set<block, BlockCompare> set_diff_result = 
            ComputeSetDifference(vec_intersection_prime, testcase.vec_intersection);  

        double error_probability = set_diff_result.size()/double(testcase.vec_intersection.size()); 
        std::cout << "mqRPMT-based PSI test succeeds with probability " << (1 - error_probability) << std::endl; 
    }


//schnorr

    PrintSplitLine('-'); 
    std::cout << "Supervision SIG test begins >>>" << std::endl; 
    PrintSplitLine('-'); 
    
    size_t TEST_NUM = 10; 
    test_schnorr(TEST_NUM);
    
    PrintSplitLine('-'); 
    std::cout << "Supervision SIG test finishes >>>" << std::endl; 
    PrintSplitLine('-'); 


    CRYPTO_Finalize();   
    
    return 0; 
}