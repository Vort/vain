#include "Crypto.h"
#include "Identity.h"
#include "I2PEndian.h"

#ifdef _WIN32
  #include "wingetopt.h"
#else
  #include <getopt.h>
#endif

#include <regex>
#include <mutex>
#include <iostream>
#include <iomanip>
#include <fstream>
#include <stdlib.h>
#include <thread>
#include <vector>
#include <ctime>
#include <atomic>

#ifdef _WIN32
  #include <windows.h>
#endif

// sha256
#define Ch(x, y, z)		((x & (y ^ z)) ^ z)
#define Maj(x, y, z)	((x & (y | z)) | (y & z))
#define SHR(x, n)		(x >> n)
#define ROTR(x, n)		((x >> n) | (x << (32 - n)))
#define S0(x)			(ROTR(x, 2) ^ ROTR(x, 13) ^ ROTR(x, 22))
#define S1(x)			(ROTR(x, 6) ^ ROTR(x, 11) ^ ROTR(x, 25))
#define s0(x)			(ROTR(x, 7) ^ ROTR(x, 18) ^ SHR(x, 3))
#define s1(x)			(ROTR(x, 17) ^ ROTR(x, 19) ^ SHR(x, 10))

#define RND(a, b, c, d, e, f, g, h, k) \
	t0 = h + S1(e) + Ch(e, f, g) + k; \
	t1 = S0(a) + Maj(a, b, c); \
	d += t0; \
	h = t0 + t1;

#define RNDr(S, W, i, k) \
	RND(S[(64 - i) % 8], S[(65 - i) % 8], \
	S[(66 - i) % 8], S[(67 - i) % 8], \
	S[(68 - i) % 8], S[(69 - i) % 8], \
	S[(70 - i) % 8], S[(71 - i) % 8], \
	W[i] + k)

#define BLOCK_SIZE 4096
#define ADDR_BUF_LEN 53
#define KEYS_FULL_LEN 679
#define DEF_OUTNAME "private.dat"

static std::atomic_bool GlobalFound(false);
static std::atomic_int HashesCount(0);
static char OutAddr[ADDR_BUF_LEN];
static uint8_t OutKeys[KEYS_FULL_LEN];
static std::mutex OutMutex;
static std::chrono::high_resolution_clock::time_point StartTime;
static std::chrono::high_resolution_clock::time_point PrevStatTime;

unsigned int count_cpu;

const uint8_t lastBlock[64] =
{
	0x05, 0x00, 0x04, 0x00, 0x07, 0x00, 0x00, 0x80, // 7 bytes EdDSA certificate 
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0C, 0x38  // 3128 bits (391 bytes)
};

static struct
{
	bool reg = false;
	int threads = -1;
	std::string outputpath = "";
	std::regex regex;
} options;

void inline CalculateW (const uint8_t block[64], uint32_t W[64])
{
/**
 * implementation of orignal
 */
	for (int i = 0; i < 16; i++)
#ifdef _WIN32
		W[i] = htobe32(((uint32_t *)(block))[i]);
#else // from big endian to little endian ( swap )
		W[i] = be32toh(((uint32_t *)(block))[i]);
#endif

	for (int i = 16; i < 64; i++)
		W[i] = s1(W[i - 2]) + W[i - 7] + s0(W[i - 15]) + W[i - 16];
}

void inline TransformBlock (uint32_t state[8], const uint32_t W[64])
{
/**
 * implementation of orignal
 */
	uint32_t S[8];
	memcpy(S, state, 32);

	uint32_t t0, t1;
	RNDr(S, W, 0, 0x428a2f98); RNDr(S, W, 1, 0x71374491); RNDr(S, W, 2, 0xb5c0fbcf); RNDr(S, W, 3, 0xe9b5dba5);
	RNDr(S, W, 4, 0x3956c25b); RNDr(S, W, 5, 0x59f111f1); RNDr(S, W, 6, 0x923f82a4); RNDr(S, W, 7, 0xab1c5ed5);
	RNDr(S, W, 8, 0xd807aa98); RNDr(S, W, 9, 0x12835b01); RNDr(S, W, 10, 0x243185be); RNDr(S, W, 11, 0x550c7dc3);
	RNDr(S, W, 12, 0x72be5d74); RNDr(S, W, 13, 0x80deb1fe); RNDr(S, W, 14, 0x9bdc06a7); RNDr(S, W, 15, 0xc19bf174);
	RNDr(S, W, 16, 0xe49b69c1); RNDr(S, W, 17, 0xefbe4786); RNDr(S, W, 18, 0x0fc19dc6); RNDr(S, W, 19, 0x240ca1cc);
	RNDr(S, W, 20, 0x2de92c6f); RNDr(S, W, 21, 0x4a7484aa); RNDr(S, W, 22, 0x5cb0a9dc); RNDr(S, W, 23, 0x76f988da);
	RNDr(S, W, 24, 0x983e5152); RNDr(S, W, 25, 0xa831c66d); RNDr(S, W, 26, 0xb00327c8); RNDr(S, W, 27, 0xbf597fc7);
	RNDr(S, W, 28, 0xc6e00bf3); RNDr(S, W, 29, 0xd5a79147); RNDr(S, W, 30, 0x06ca6351); RNDr(S, W, 31, 0x14292967);
	RNDr(S, W, 32, 0x27b70a85); RNDr(S, W, 33, 0x2e1b2138); RNDr(S, W, 34, 0x4d2c6dfc); RNDr(S, W, 35, 0x53380d13);
	RNDr(S, W, 36, 0x650a7354); RNDr(S, W, 37, 0x766a0abb); RNDr(S, W, 38, 0x81c2c92e); RNDr(S, W, 39, 0x92722c85);
	RNDr(S, W, 40, 0xa2bfe8a1); RNDr(S, W, 41, 0xa81a664b); RNDr(S, W, 42, 0xc24b8b70); RNDr(S, W, 43, 0xc76c51a3);
	RNDr(S, W, 44, 0xd192e819); RNDr(S, W, 45, 0xd6990624); RNDr(S, W, 46, 0xf40e3585); RNDr(S, W, 47, 0x106aa070);
	RNDr(S, W, 48, 0x19a4c116); RNDr(S, W, 49, 0x1e376c08); RNDr(S, W, 50, 0x2748774c); RNDr(S, W, 51, 0x34b0bcb5);
	RNDr(S, W, 52, 0x391c0cb3); RNDr(S, W, 53, 0x4ed8aa4a); RNDr(S, W, 54, 0x5b9cca4f); RNDr(S, W, 55, 0x682e6ff3);
	RNDr(S, W, 56, 0x748f82ee); RNDr(S, W, 57, 0x78a5636f); RNDr(S, W, 58, 0x84c87814); RNDr(S, W, 59, 0x8cc70208);
	RNDr(S, W, 60, 0x90befffa); RNDr(S, W, 61, 0xa4506ceb); RNDr(S, W, 62, 0xbef9a3f7); RNDr(S, W, 63, 0xc67178f2);

	for (int i = 0; i < 8; i++)	state[i] += S[i];
}

void inline HashNextBlock (uint32_t state[8], const uint8_t * block)
{
/**
 * implementation of orignal
 */
	uint32_t W[64];
	CalculateW (block, W);
	TransformBlock (state, W);
}

bool check_prefix(const char * buf)
{
	unsigned short size_str = 0;
	while(*buf)
	{
		if(!((*buf > 49 && *buf < 56) || (*buf > 96 && *buf < 123)) || size_str > 52)
			return false;
		size_str++;
		buf++;
	}
	return true;
}

inline size_t ByteStreamToBase32 (const uint8_t * inBuf, size_t len, char * outBuf, size_t outLen)
{
	size_t ret = 0, pos = 1;
	int bits = 8, tmp = inBuf[0];
	while (ret < outLen && (bits > 0 || pos < len))
	{
		if (bits < 5)
		{
			if (pos < len)
			{
				tmp <<= 8;
				tmp |= inBuf[pos] & 0xFF;
				pos++;
				bits += 8;
			}
			else // last byte
			{
				tmp <<= (5 - bits);
				bits = 5;
			}
		}

		bits -= 5;
		int ind = (tmp >> bits) & 0x1F;
		outBuf[ret] = (ind < 26) ? (ind + 'a') : ((ind - 26) + '2');
		ret++;
	}
	outBuf[ret]='\0';
	return ret;
}

inline bool NotThat(const char * what, const std::regex & reg){
	return std::regex_match(what,reg) == 1 ? false : true;
}

inline bool NotThat(const char * a, const char *b)
{
	while(*b)
		if(*a++!=*b++)
			return true;
	return false;
}

void ShowStats(int threadCount, const std::string pattern)
{
	bool statLineDisplayed = false;
	std::cout << "Threads: " << threadCount << " | Pattern: " << pattern << std::endl;
	for (;;)
	{
		for (int i = 0; i < 5; i++)
		{
			if (GlobalFound)
				break;
			std::this_thread::sleep_for(std::chrono::milliseconds(200));
		}
		if (GlobalFound)
			break;
		auto now = std::chrono::high_resolution_clock::now();
		double usecElapsedSincePrevStat = std::chrono::duration_cast<
			std::chrono::microseconds>(now - PrevStatTime).count();
		double mhps = HashesCount / usecElapsedSincePrevStat;
		HashesCount = 0;
		PrevStatTime = now;

		auto elapsed = now - StartTime;
		auto hrs = std::chrono::duration_cast<std::chrono::hours>(elapsed);
		auto mins = std::chrono::duration_cast<std::chrono::minutes>(elapsed - hrs);
		auto secs = std::chrono::duration_cast<std::chrono::seconds>(elapsed - hrs - mins);

		std::cout << "\rElapsed: ";
		std::cout << std::setfill('0') << std::right;
		std::cout << std::setw(2) << hrs.count() << ":";
		std::cout << std::setw(2) << mins.count() << ":";
		std::cout << std::setw(2) << secs.count();
		std::cout << " | " << "Speed: ";
		std::cout << std::setfill(' ');
		std::cout << std::setw(6) << std::fixed << std::setprecision(2) << mhps << " MH/s";
		std::cout << std::flush;
		statLineDisplayed = true;
	}
	if (statLineDisplayed)
		std::cout << std::endl;
}

bool thread_find(const char * prefix)
{
	auto keys = i2p::data::PrivateKeys::CreateRandomKeys(i2p::data::SIGNING_KEY_TYPE_EDDSA_SHA512_ED25519);

	uint8_t keysBuf[KEYS_FULL_LEN];
	keys.ToBuffer(keysBuf, keys.GetFullLen());

	uint32_t hash[8];

	size_t len = 52;
	
	if (!options.reg)
		len = strlen(prefix);

	// precalculate first 5 blocks (320 bytes)
	uint32_t state[8] = { 0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19 };
	HashNextBlock (state, keysBuf);
	HashNextBlock (state, keysBuf + 64);
	HashNextBlock (state, keysBuf + 128);
	HashNextBlock (state, keysBuf + 192);
	HashNextBlock (state, keysBuf + 256);

	// pre-calculate last W
	uint32_t lastW[64];
	CalculateW (lastBlock, lastW);

	uint64_t* nonce = (uint64_t*)(keysBuf + 320);
	char addr[ADDR_BUF_LEN];
	uint32_t state1[8];

	while (!GlobalFound)
	{
		bool localFound = false;
		for (int i = 0; i < BLOCK_SIZE; i++)
		{
			memcpy(state1, state, 32);
			// calculate hash of block with nonce
			HashNextBlock(state1, keysBuf + 320);
			// apply last block
			TransformBlock(state1, lastW);
			// get final hash
			for (int j = 8; j--;)
				hash[j] = htobe32(state1[j]);
			ByteStreamToBase32((uint8_t*)hash, 32, addr, len);

			if (options.reg ? !NotThat(addr, options.regex) : !NotThat(addr, prefix))
			{
				std::unique_lock<std::mutex> l(OutMutex);
				ByteStreamToBase32((uint8_t*)hash, 32, OutAddr, 52);
				memcpy(OutKeys, keysBuf, KEYS_FULL_LEN);
				localFound = true;
			}

			(*nonce)++;
		}
		if (localFound)
			GlobalFound = true;
		HashesCount += BLOCK_SIZE;
	}
	
	return true;
}

void usage()
{
	const constexpr char * help="Usage:\n"
    "  vain [text-pattern|regex-pattern] [options]\n\n"
    "OPTIONS:\n"
	"  -h --help      show this help (same as --usage)\n"
	"  -r --reg       use regexp instead of simple text pattern, ex.: vain '(one|two).*' -r\n"
	"  -t --threads   number of threads to use (default: one per processor)\n"
	"  -o --output    privkey output file name (default: ./" DEF_OUTNAME ")\n"
	"";
	puts(help);
}

void parsing(int argc, char ** args)
{
	int option_index;
	static struct option long_options[]={
		{"help",no_argument,0,'h'},
		{"reg", no_argument,0,'r'},
		{"threads", required_argument, 0, 't'},
		{"output", required_argument,0,'o'},
		{"usage", no_argument,0,0},
		{0,0,0,0}
	};

	int c;
	while( (c=getopt_long(argc,args, "hrt:s:o:", long_options, &option_index))!=-1){
		switch(c){
			case 0:
				if ( std::string(long_options[option_index].name) == std::string("usage") ){
					usage();
					exit(1);
				}
			case 'h':
				usage();
				exit(0);
				break;
			case 'r':
				options.reg=true;
				break;
			case 't':
				options.threads=atoi(optarg);
				break;
			case 'o':
				options.outputpath=optarg;
				break;
			case '?':
				std::cerr << "Undefined argument" << std::endl;
			default:
				std::cerr << args[0] << " --usage / --help" << std::endl;
				exit(1);
				break;
		}
	}
}

int main (int argc, char * argv[])
{
	if (argc < 2)
	{
		usage();
		return 0;
	}
    
	parsing( argc > 2 ? argc-1 : argc, argc > 2 ? argv+1 : argv);
	//
	if (!options.reg && !check_prefix( argv[1] ))
	{
		std::cout << "Invalid pattern." << std::endl;
		usage();
		return 1;
	} else {
		options.regex=std::regex(argv[1]);
	}

	i2p::crypto::InitCrypto (false, true, true, false);

	if (options.threads <= 0)
		options.threads = std::thread::hardware_concurrency();

	StartTime = std::chrono::high_resolution_clock::now();
	PrevStatTime = StartTime;
	std::vector<std::thread> threads(options.threads);
	for (int j = 0; j < options.threads; j++)
		threads[j] = std::thread(thread_find, argv[1]);

	ShowStats(options.threads, argv[1]);
    
	for (int j = 0; j < options.threads; j++)
		threads[j].join();

	std::cout << "Found address: " << OutAddr << std::endl;

	if (options.outputpath.empty())
		options.outputpath.assign(DEF_OUTNAME);

	std::ofstream f (options.outputpath, std::ofstream::binary);
	if (f)
		f.write ((char *)OutKeys, KEYS_FULL_LEN);
	else
		std::cout << "Can't create output file: " << options.outputpath << std::endl;

	i2p::crypto::TerminateCrypto ();

	return 0;
}
