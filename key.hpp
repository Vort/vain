#ifndef I2PD_TOOLS_COMMON_KEY_HPP
#define I2PD_TOOLS_COMMON_KEY_HPP
#include "Identity.h"
#include <algorithm>
#include <cctype>
#include <sstream>
#include <string>


/** @brief returns string representation of a signing key type */
std::string SigTypeToName(uint16_t keytype)
{
	switch(keytype) {
	case i2p::data::SIGNING_KEY_TYPE_DSA_SHA1:
		return "DSA-SHA1";
	case i2p::data::SIGNING_KEY_TYPE_ECDSA_SHA256_P256:
		return "ECDSA-P256";
	case i2p::data::SIGNING_KEY_TYPE_ECDSA_SHA384_P384:
		return "ECDSA-P384";
	case i2p::data::SIGNING_KEY_TYPE_ECDSA_SHA512_P521:
		return "ECDSA-P521";
	case i2p::data::SIGNING_KEY_TYPE_RSA_SHA256_2048:
		return "RSA-2048-SHA256";
	case i2p::data::SIGNING_KEY_TYPE_RSA_SHA384_3072:
		return "RSA-3072-SHA384";
	case i2p::data::SIGNING_KEY_TYPE_RSA_SHA512_4096:
		return "RSA-4096-SHA512";
	case i2p::data::SIGNING_KEY_TYPE_EDDSA_SHA512_ED25519:
		return "ED25519-SHA512";
	case i2p::data::SIGNING_KEY_TYPE_GOSTR3410_CRYPTO_PRO_A_GOSTR3411_256:
		return "GOSTR3410-A-GOSTR3411-256";
	case i2p::data::SIGNING_KEY_TYPE_GOSTR3410_TC26_A_512_GOSTR3411_512:
		return "GOSTR3410-TC26-A-GOSTR3411-512";
	case i2p::data::SIGNING_KEY_TYPE_REDDSA_SHA512_ED25519:
		return "RED25519-SHA512";
	default:
		std::stringstream ss;
		ss << "unknown: " << keytype;
		return ss.str();
	}
}

/** @brief make string uppercase */
static void ToUpper(std::string & str)
{
	std::transform(str.begin(), str.end(), str.begin(), [] (uint8_t ch) {
		return std::toupper(ch);
	});
}
/** @brief returns the signing key number given its name or -1 if there is no key of that type */
uint16_t NameToSigType(const std::string & keyname)
{
	if(keyname.size() <= 2) return atoi(keyname.c_str());

	std::string name = keyname;
	ToUpper(name);
	auto npos = std::string::npos;
	if(name.find("DSA") == 0) return i2p::data::SIGNING_KEY_TYPE_DSA_SHA1;

	if(name.find("P256") != npos) return i2p::data::SIGNING_KEY_TYPE_ECDSA_SHA256_P256;

	if(name.find("P384") != npos) return i2p::data::SIGNING_KEY_TYPE_ECDSA_SHA384_P384;

	if(name.find("RSA-SHA265") != npos) return i2p::data::SIGNING_KEY_TYPE_RSA_SHA256_2048;

	if(name.find("RSA-SHA384") != npos) return i2p::data::SIGNING_KEY_TYPE_RSA_SHA384_3072;

	if(name.find("RSA-SHA512") != npos) return i2p::data::SIGNING_KEY_TYPE_RSA_SHA512_4096;

	if(name.find("ED25519") != npos) return i2p::data::SIGNING_KEY_TYPE_EDDSA_SHA512_ED25519;

	if(name.find("GOSTR3410-A-GOSTR3411-256") != npos) return i2p::data::SIGNING_KEY_TYPE_GOSTR3410_CRYPTO_PRO_A_GOSTR3411_256;

	if(name.find("GOSTR3410-TC26-A-GOSTR3411-512") != npos) return i2p::data::SIGNING_KEY_TYPE_GOSTR3410_TC26_A_512_GOSTR3411_512;

	if(name.find("RED25519") != npos) return i2p::data::SIGNING_KEY_TYPE_REDDSA_SHA512_ED25519;	

	return -1;
}

#endif
