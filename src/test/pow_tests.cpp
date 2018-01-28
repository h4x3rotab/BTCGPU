// Copyright (c) 2015 The Bitcoin Core developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "chain.h"
#include "chainparams.h"
#include "pow.h"
#include "random.h"
#include "util.h"
#include "test/test_bitcoin.h"

#include <boost/test/unit_test.hpp>

BOOST_FIXTURE_TEST_SUITE(pow_tests, BasicTestingSetup)

/* Test calculation of next difficulty target with no constraints applying */
BOOST_AUTO_TEST_CASE(get_next_work)
{
    const auto chainParams = CreateChainParams(CBaseChainParams::MAIN);
    int64_t nLastRetargetTime = 1261130161; // Block #30240
    CBlockIndex pindexLast;
    pindexLast.nHeight = 32255;
    pindexLast.nTime = 1262152739;  // Block #32255
    pindexLast.nBits = 0x1d00ffff;
    BOOST_CHECK_EQUAL(BitcoinCalculateNextWorkRequired(&pindexLast, nLastRetargetTime, chainParams->GetConsensus()), 0x1d00d86a);
}

/* Test the constraint on the upper bound for next work */
BOOST_AUTO_TEST_CASE(get_next_work_pow_limit)
{
    const auto chainParams = CreateChainParams(CBaseChainParams::MAIN);
    int64_t nLastRetargetTime = 1231006505; // Block #0
    CBlockIndex pindexLast;
    pindexLast.nHeight = 2015;
    pindexLast.nTime = 1233061996;  // Block #2015
    pindexLast.nBits = 0x1d00ffff;
    BOOST_CHECK_EQUAL(BitcoinCalculateNextWorkRequired(&pindexLast, nLastRetargetTime, chainParams->GetConsensus()), 0x1d00ffff);
}

/* Test the constraint on the lower bound for actual time taken */
BOOST_AUTO_TEST_CASE(get_next_work_lower_limit_actual)
{
    const auto chainParams = CreateChainParams(CBaseChainParams::MAIN);
    int64_t nLastRetargetTime = 1279008237; // Block #66528
    CBlockIndex pindexLast;
    pindexLast.nHeight = 68543;
    pindexLast.nTime = 1279297671;  // Block #68543
    pindexLast.nBits = 0x1c05a3f4;
    BOOST_CHECK_EQUAL(BitcoinCalculateNextWorkRequired(&pindexLast, nLastRetargetTime, chainParams->GetConsensus()), 0x1c0168fd);
}

/* Test the constraint on the upper bound for actual time taken */
BOOST_AUTO_TEST_CASE(get_next_work_upper_limit_actual)
{
    const auto chainParams = CreateChainParams(CBaseChainParams::MAIN);
    int64_t nLastRetargetTime = 1263163443; // NOTE: Not an actual block time
    CBlockIndex pindexLast;
    pindexLast.nHeight = 46367;
    pindexLast.nTime = 1269211443;  // Block #46367
    pindexLast.nBits = 0x1c387f6f;
    BOOST_CHECK_EQUAL(BitcoinCalculateNextWorkRequired(&pindexLast, nLastRetargetTime, chainParams->GetConsensus()), 0x1d00e1fd);
}

BOOST_AUTO_TEST_CASE(GetBlockProofEquivalentTime_test)
{
    const auto chainParams = CreateChainParams(CBaseChainParams::MAIN);
    std::vector<CBlockIndex> blocks(10000);
    for (int i = 0; i < 10000; i++) {
        blocks[i].pprev = i ? &blocks[i - 1] : nullptr;
        blocks[i].nHeight = i;
        blocks[i].nTime = 1269211443 + i * chainParams->GetConsensus().nPowTargetSpacing;
        blocks[i].nBits = 0x207fffff; /* target 0x7fffff000... */
        blocks[i].nChainWork = i ? blocks[i - 1].nChainWork + GetBlockProof(blocks[i - 1]) : arith_uint256(0);
    }

    for (int j = 0; j < 1000; j++) {
        CBlockIndex *p1 = &blocks[InsecureRandRange(10000)];
        CBlockIndex *p2 = &blocks[InsecureRandRange(10000)];
        CBlockIndex *p3 = &blocks[InsecureRandRange(10000)];

        int64_t tdiff = GetBlockProofEquivalentTime(*p1, *p2, *p3, chainParams->GetConsensus());
        BOOST_CHECK_EQUAL(tdiff, p1->GetBlockTime() - p2->GetBlockTime());
    }
}

// Jacob's EMA

/* Check the precision of f128 Tyler series */
BOOST_AUTO_TEST_CASE(f128_neg_exp_test)
{
    long double b64 = powl(2, 64);
    long double b128 = powl(2, 128);
    for (long double x = 0.2; x < 0.8; x += 0.001L) {
        arith_uint256 f128((uint64_t)(x * b64));
        f128 <<= 64;
        arith_uint256 f128_result = f128_neg_exp(f128, 25);
        long double test_result = f128_result.getdouble() / b128;
        long double real_result = expl(-x);
        BOOST_CHECK_LE((test_result - real_result) / real_result, 1e-8l);  // 1e-8 ~= 1 / 0xffffff
    }
}

/* Check no significant delta% of the fixed point calculation */
void CheckJacobEmaCalculateDelta(uint32_t previous_target, uint64_t solve_time)
{
    const long double dmax = powl(2, 256-1);
    int T = 600;
    int N = 50;
    uint32_t target = JacobEmaCalculateNextWorkRequired(T, N, solve_time, previous_target);
    arith_uint256 u256_target;
    u256_target.SetCompact(target);
    long double test_diff = dmax / u256_target.getdouble();

    arith_uint256 u256_previous_target;
    u256_previous_target.SetCompact(previous_target);
    long double prev_diff = dmax / u256_previous_target.getdouble();
    long double ST = solve_time;
    long double T_ = T;
    long double real_diff = prev_diff * (T_ / ST + expl(-2.0L * ST / (T_ * N)) * (1.0L - T_ / ST));

    BOOST_CHECK_LE((test_diff - real_diff) / real_diff, 1e-6l);
}

/* Check the Jacob's EMA calculation */
BOOST_AUTO_TEST_CASE(JacobEmaCalculateNextWorkRequired_test)
{
    for (uint32_t previous_target = 0x10333333; previous_target <= 0x1d333333; previous_target += 0x01000000) {
        CheckJacobEmaCalculateDelta(previous_target, 755);
    }
    for (uint64_t solve_time = 10; solve_time <= 3600; solve_time += 100) {
        CheckJacobEmaCalculateDelta(0x1d333333, solve_time);
    }
}

BOOST_AUTO_TEST_SUITE_END()
