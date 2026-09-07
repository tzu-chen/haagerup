// Exact enumeration of an exported affine binary space of Cayley functions.
// Full-Q outputs require a separate complete cubic verifier.
#include <algorithm>
#include <bit>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <vector>

int main(int argc, char** argv) {
    if (argc != 2) throw std::runtime_error("usage: search data.txt");
    std::ifstream input(argv[1]);
    uint32_t n, modulus, delta, generator, dimension, count;
    if (!(input >> n >> modulus >> delta >> generator >> dimension >> count))
        throw std::runtime_error("invalid header");
    if (dimension >= 63) throw std::runtime_error("enumeration dimension too large");
    const uint32_t degree = std::bit_width(modulus)-1;
    const uint32_t size = uint32_t(1) << degree;
    const uint32_t order = size-1;
    const uint32_t invalid = std::numeric_limits<uint32_t>::max();
    std::vector<uint32_t> current(n-1), indices(n-1);
    for (auto& value : current) input >> value;
    for (auto& value : indices) input >> value;
    for (auto value : indices)
        if (value >= n) throw std::runtime_error("invalid domain index");
    std::vector<std::vector<uint32_t>> basis(dimension, std::vector<uint32_t>(n-1));
    for (auto& row : basis) for (auto& value : row) input >> value;
    auto multiply = [modulus, size](uint32_t a, uint32_t b) {
        uint32_t result = 0;
        while (b) {
            if (b & 1) result ^= a;
            b >>= 1; a <<= 1;
            if (a & size) a ^= modulus;
        }
        return result;
    };
    std::vector<uint32_t> logarithm(size, invalid), power(order);
    uint32_t element = 1;
    for (uint32_t j = 0; j < order; ++j) {
        if (element == 0 || logarithm[element] != invalid)
            throw std::runtime_error("invalid primitive element or field polynomial");
        logarithm[element] = j; power[j] = element;
        element = multiply(element, generator);
    }
    if (element != 1) throw std::runtime_error("power cycle did not close");
    std::vector<uint32_t> phase_log(size, invalid);
    for (uint32_t j = 0; j < (n-1)*(n-1); ++j) {
        uint32_t key, value; input >> key >> value;
        if (key >= size || value == 0 || value >= size || phase_log[key] != invalid)
            throw std::runtime_error("invalid Cayley table");
        phase_log[key] = logarithm[value];
    }
    struct Term { uint32_t a,b,c,d; };
    std::vector<std::vector<Term>> equations(count);
    auto residue = [n](int64_t value) { value %= n; return uint32_t(value < 0 ? value+n : value); };
    for (auto& equation : equations) {
        uint32_t g,h; input >> g >> h;
        for (uint32_t m=0; m<n; ++m)
            equation.push_back({m,residue(int64_t(h)-m),residue(-int64_t(m)-g),residue(int64_t(m)+g-h)});
    }
    if (!input) throw std::runtime_error("incomplete input");
    std::vector<uint32_t> logs(n), phases(n);
    auto vanishes = [&logs, &power, order](const std::vector<Term>& equation) {
        uint32_t sum = 0;
        for (const auto& term : equation) {
            uint32_t exponent = logs[term.a]+logs[term.b]+logs[term.c]+logs[term.d];
            while (exponent >= order) exponent -= order;
            sum ^= power[exponent];
        }
        return sum == 0;
    };
    uint64_t first = 0, full = 0;
    const uint64_t total = uint64_t(1) << dimension;
    auto start = std::chrono::steady_clock::now();
    for (uint64_t index=0; index<total; ++index) {
        if (index) {
            const auto& direction = basis[std::countr_zero(index)];
            for (uint32_t j=0; j<n-1; ++j) current[j] ^= direction[j];
        }
        logs[0] = 0;
        for (uint32_t a=1; a<n; ++a) {
            // The extra domain index denotes the Cayley point at infinity.
            logs[a] = indices[a-1] == n-1 ? logarithm[multiply(delta,delta)]
                                         : phase_log[current[indices[a-1]]];
            if (logs[a] == invalid) throw std::runtime_error("function left the exported subfield");
        }
        if (!vanishes(equations[0])) continue;
        ++first;
        bool ok = true;
        for (uint32_t j=1; j<count; ++j)
            if (!vanishes(equations[j])) { ok = false; break; }
        if (!ok) continue;
        for (uint32_t a=0; a<n; ++a) phases[a] = power[logs[a]];
        for (uint32_t a=1; a<n; ++a) {
            if (multiply(phases[a],phases[n-a]) != delta ||
                power[(4ULL*logs[a])%order] != phases[(2*a)%n])
                throw std::runtime_error("norm/Frobenius check failed");
        }
        ++full;
        std::cout << "FULL_Q {\"n\":" << n << ",\"mask\":" << (index^(index>>1)) << ",\"W\":[";
        for (uint32_t a=0; a<n; ++a) std::cout << (a ? "," : "") << phases[a];
        std::cout << "]}" << std::endl;
    }
    double elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    std::cout << "COMPLETE n=" << n << " candidates=" << total << " first_Q=" << first
              << " full_Q=" << full << " seconds=" << elapsed << std::endl;
}
