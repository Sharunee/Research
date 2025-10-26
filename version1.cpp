#include <iostream>
#include <chrono>
#include <cstdint>
#include <random>
#include <cstring>
#include <vector>
#include <string>
#include <iomanip>
using namespace std;
using Clock = chrono::high_resolution_clock;


struct ECCPoint { uint64_t x, y; };
struct ECCKeys  { uint64_t priv; ECCPoint pub; };

const uint64_t P = 9739;
const uint64_t Acoef = 497;
const uint64_t Bcoef = 1768;
const ECCPoint G = {1804, 5368};

uint64_t mod_inv(uint64_t a, uint64_t m) {
    int64_t t = 0, newt = 1;
    int64_t r = m, newr = a;
    while (newr != 0) {
        int64_t q = r / newr;
        int64_t tmp = t; t = newt; newt = tmp - q * newt;
        tmp = r; r = newr; newr = tmp - q * newr;
    }
    if (r > 1) return 0;
    if (t < 0) t += m;
    return (uint64_t)t;
}

ECCPoint ecc_add(const ECCPoint &P1, const ECCPoint &P2) {
    if (P1.x == P2.x && P1.y == P2.y) {
        uint64_t denom = (2 * P1.y) % P;
        uint64_t inv = mod_inv(denom, P);
        uint64_t m = ((3 * (P1.x * P1.x % P) + Acoef) % P) * inv % P;
        int64_t x3 = (int64_t)((m * m + P - (2 * P1.x % P)) % P);
        int64_t y3 = (int64_t)((m * (P1.x + P - (uint64_t)x3) + P - P1.y) % P);
        if (x3 < 0) x3 += P;
        if (y3 < 0) y3 += P;
        return {(uint64_t)x3, (uint64_t)y3};
    } else {
        uint64_t num = (P2.y + P - P1.y) % P;
        uint64_t den = (P2.x + P - P1.x) % P;
        uint64_t inv = mod_inv(den, P);
        uint64_t m = num * inv % P;
        uint64_t x3 = ( (m * m) + P - P1.x + P - P2.x ) % P;
        uint64_t y3 = ( (m * (P1.x + P - x3)) + P - P1.y ) % P;
        return {x3, y3};
    }
}

ECCPoint ecc_mul(const ECCPoint &point, uint64_t k) {
    ECCPoint R = {0, 0};
    ECCPoint addend = point;
    for (int i = 0; i < 64; ++i) {
        if ((k >> i) & 1ULL) {
            if (R.x == 0 && R.y == 0) R = addend;
            else R = ecc_add(R, addend);
        }
        addend = ecc_add(addend, addend);
    }
    return R;
}

ECCKeys ecc_generate(mt19937_64 &rng) {
    uniform_int_distribution<uint64_t> dist(2, P - 1);
    ECCKeys k;
    k.priv = dist(rng);
    k.pub = ecc_mul(G, k.priv);
    return k;
}


static const uint8_t S[16]     = {0xC,5,6,0xB,9,0,0xA,0xD,3,0xE,0xF,8,4,7,1,2};
static const uint8_t S_inv[16] = {5,0xE,0xF,8,0xC,1,2,0xD,0xB,4,6,3,0,7,9,10};

void key_schedule(uint8_t key[10], uint64_t roundKeys[32]) {
    uint8_t k[10];
    memcpy(k, key, 10);
    for (int round = 0; round <= 31; ++round) {
        uint64_t rk = 0;
        for (int i = 0; i < 8; ++i) rk = (rk << 8) | k[i];
        roundKeys[round] = rk;
        if (round == 31) break;
        // rotate left 61
        uint64_t high = 0;
        for (int i = 0; i < 8; ++i) high = (high << 8) | k[i];
        uint16_t low = (k[8] << 8) | k[9];
        uint64_t new_high = ((high << 61) | (low >> 3)) & 0xFFFFFFFFFFFFFFFFULL;
        uint16_t new_low = (uint16_t)(((high >> 3) & 0x1FFF) | ((low << 13) & 0xFFFF));
        for (int i = 7; i >= 0; --i) { k[i] = new_high & 0xFF; new_high >>= 8; }
        k[8] = (new_low >> 8) & 0xFF; k[9] = new_low & 0xFF;
        // S-box on top nibble
        k[0] = (S[k[0] >> 4] << 4) | (k[0] & 0x0F);
        // XOR round counter
        k[7] ^= (round + 1) >> 1;
        k[8] ^= ((round + 1) & 1) << 7;
    }
}

uint64_t present_encrypt_block(uint64_t block, uint8_t key[10]) {
    uint64_t roundKeys[32]; key_schedule(key, roundKeys);
    for (int r = 0; r < 31; ++r) {
        block ^= roundKeys[r];
        uint64_t tmp = 0;
        for (int i = 0; i < 16; ++i) {
            uint8_t n = (block >> (4 * i)) & 0xF;
            tmp |= (uint64_t)S[n] << (4 * i);
        }
        uint64_t perm = 0;
        for (int i = 0; i < 63; ++i)
            if (tmp & (1ULL << i))
                perm |= (1ULL << ((i * 16) % 63));
        if (tmp & (1ULL << 63)) perm |= (1ULL << 63);
        block = perm;
    }
    block ^= roundKeys[31];
    return block;
}

uint64_t present_decrypt_block(uint64_t block, uint8_t key[10]) {
    uint64_t roundKeys[32]; key_schedule(key, roundKeys);
    block ^= roundKeys[31];
    for (int r = 30; r >= 0; --r) {
        uint64_t tmp = 0;
        for (int i = 0; i < 63; ++i)
            if (block & (1ULL << i))
                tmp |= (1ULL << ((i * 4) % 63));
        if (block & (1ULL << 63)) tmp |= (1ULL << 63);
        uint64_t s_inv_res = 0;
        for (int i = 0; i < 16; ++i) {
            uint8_t n = (tmp >> (4 * i)) & 0xF;
            s_inv_res |= (uint64_t)S_inv[n] << (4 * i);
        }
        block = s_inv_res ^ roundKeys[r];
    }
    return block;
}


uint64_t pack_block_le(const uint8_t bytes[8]) {
    uint64_t v = 0;
    for (int i = 0; i < 8; ++i) v |= (uint64_t)bytes[i] << (8 * i);
    return v;
}
void unpack_block_le(uint64_t v, uint8_t out[8]) {
    for (int i = 0; i < 8; ++i) out[i] = (v >> (8 * i)) & 0xFF;
}

vector<uint8_t> pkcs7_pad(const vector<uint8_t> &data) {
    size_t n = data.size();
    size_t pad_len = 8 - (n % 8);
    if (pad_len == 0) pad_len = 8;
    vector<uint8_t> out = data;
    out.resize(n + pad_len, (uint8_t)pad_len);
    return out;
}
vector<uint8_t> pkcs7_unpad(const vector<uint8_t> &data) {
    if (data.empty()) return {};
    uint8_t pad = data.back();
    if (pad == 0 || pad > 8) return data; // invalid - return as-is
    size_t n = data.size();
    for (size_t i = 0; i < pad; ++i) {
        if (data[n - 1 - i] != pad) return data; // invalid - return as-is
    }
    return vector<uint8_t>(data.begin(), data.end() - pad);
}


int main() {
    
    cout << "Enter plaintext : ";
    string input;
    if (!getline(cin, input)) {
        cerr << "No input provided.\n";
        return 1;
    }

    vector<uint8_t> plain_bytes(input.begin(), input.end());
    vector<uint8_t> padded = pkcs7_pad(plain_bytes);

    mt19937_64 rng(chrono::steady_clock::now().time_since_epoch().count());
    auto t_start_total = Clock::now();

    
    auto t_k0 = Clock::now();
    ECCKeys A = ecc_generate(rng);
    auto t_k1 = Clock::now();
    ECCKeys B = ecc_generate(rng);
    auto t_k2 = Clock::now();

 
    ECCPoint sharedA = ecc_mul(B.pub, A.priv);
    ECCPoint sharedB = ecc_mul(A.pub, B.priv);
    auto t_k3 = Clock::now();

    
    uint8_t key[10];
    for (int i = 0; i < 10; ++i) key[i] = (sharedA.x >> (i * 5)) & 0xFF;

    
    auto t_enc_start = Clock::now();
    vector<uint64_t> cipher_blocks;
    for (size_t off = 0; off < padded.size(); off += 8) {
        uint8_t block_bytes[8];
        for (int i = 0; i < 8; ++i) block_bytes[i] = padded[off + i];
        uint64_t blk = pack_block_le(block_bytes);
        uint64_t c = present_encrypt_block(blk, key);
        cipher_blocks.push_back(c);
    }
    auto t_enc_end = Clock::now();

    auto t_dec_start = Clock::now();
    vector<uint8_t> recovered_bytes;
    for (uint64_t c : cipher_blocks) {
        uint64_t m = present_decrypt_block(c, key);
        uint8_t outb[8];
        unpack_block_le(m, outb);
        for (int i = 0; i < 8; ++i) recovered_bytes.push_back(outb[i]);
    }
    auto t_dec_end = Clock::now();

  
    vector<uint8_t> recovered_unpad = pkcs7_unpad(recovered_bytes);
    auto t_end_total = Clock::now();

   
    auto keygenA_us = chrono::duration_cast<chrono::microseconds>(t_k1 - t_k0).count();
    auto keygenB_us = chrono::duration_cast<chrono::microseconds>(t_k2 - t_k1).count();
    auto exchange_us = chrono::duration_cast<chrono::microseconds>(t_k3 - t_k2).count();
    auto present_enc_us = chrono::duration_cast<chrono::microseconds>(t_enc_end - t_enc_start).count();
    auto present_dec_us = chrono::duration_cast<chrono::microseconds>(t_dec_end - t_dec_start).count();
    auto total_us = chrono::duration_cast<chrono::microseconds>(t_end_total - t_start_total).count();

   
    cout << "\n=== ECC + PRESENT Results ===\n";
    cout << hex << nouppercase;
    cout << "Public Key A: (" << A.pub.x << ", " << A.pub.y << ")\n";
    cout << "Public Key B: (" << B.pub.x << ", " << B.pub.y << ")\n";
    cout << "Shared Secret A.x: " << sharedA.x << "\n";
    cout << "Shared Secret B.x: " << sharedB.x << "\n";

    cout << dec << "\nPlaintext (len " << plain_bytes.size() << "): " << input << "\n";

    
    cout << "Ciphertext (" << cipher_blocks.size() << " blocks): 0x";
    for (uint64_t c : cipher_blocks) {
       
        for (int i = 0; i < 8; ++i) {
            uint8_t b = (c >> (8 * i)) & 0xFF;
            cout << setw(2) << setfill('0') << hex << (int)b;
        }
    }
    cout << dec << "\n";

   
    string recovered_str(recovered_unpad.begin(), recovered_unpad.end());
    cout << "Decrypted (len " << recovered_unpad.size() << "): " << recovered_str << "\n\n";

    cout << "=== Timing Summary (microseconds) ===\n";
    cout << "ECC KeyGen A : " << keygenA_us << " µs\n";
    cout << "ECC KeyGen B : " << keygenB_us << " µs\n";
    cout << "ECC Exchange : " << exchange_us << " µs\n";
    cout << "PRESENT Encrypt (all blocks): " << present_enc_us << " µs\n";
    cout << "PRESENT Decrypt (all blocks): " << present_dec_us << " µs\n";
    cout << "Total (all stages) : " << total_us << " µs\n";
    
    
    if (recovered_unpad == plain_bytes) {
        cout << "SUCCESS: Decrypted text matches input.\n";
    } else {
        cout << "WARNING: Decrypted text differs from input.\n";
    }

    return 0;
}
