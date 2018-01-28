// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "pow.h"

#include "arith_uint256.h"
#include "chain.h"
#include "chainparams.h"
#include "crypto/equihash.h"
#include "primitives/block.h"
#include "streams.h"
#include "uint256.h"
#include "util.h"
#include <algorithm>

#include <algorithm>
#include <iostream>

unsigned int GetNextWorkRequired(const CBlockIndex* pindexLast, const CBlockHeader *pblock,
                                 const Consensus::Params& params)
{
    assert(pindexLast != nullptr);
    int nHeight = pindexLast->nHeight + 1;
    bool postfork = nHeight >= params.BTGHeight;

    if (postfork == false) {
        // Original Bitcion PoW.
        return BitcoinGetNextWorkRequired(pindexLast, pblock, params);
    }
    else if (nHeight < params.BTGHeight + params.BTGPremineWindow) {
        // PoW limit for premine period.
        unsigned int nProofOfWorkLimit = UintToArith256(params.PowLimit(true)).GetCompact();
        return nProofOfWorkLimit;
    }
    else if (nHeight < params.BTGHeight + params.BTGPremineWindow + params.nDigishieldAveragingWindow) {
        // Pow limit start for warm-up period.
        return UintToArith256(params.powLimitStart).GetCompact();
    }
    else if (nHeight < params.BTGJacobEmaHeight) {
        // Regular Digishield v3.
        return DigishieldGetNextWorkRequired(pindexLast, pblock, params);
    } else {
        // Jacob's EMA.
        return JacobEmaGetNextWorkRequired(pindexLast, pblock, params);
    }
}

unsigned int JacobEmaGetNextWorkRequired(const CBlockIndex* pindexLast, const CBlockHeader *pblock,
                                         const Consensus::Params& params)
{
    assert(pindexLast != nullptr);
    unsigned int nProofOfWorkLimit = UintToArith256(params.PowLimit(true)).GetCompact();

    if (params.fPowAllowMinDifficultyBlocks) {
        // Special difficulty rule for testnet:
        // If the new block's timestamp is more than 2*10 minutes
        // then allow mining of a min-difficulty block.
        if (pblock->GetBlockTime() > pindexLast->GetBlockTime() + params.nPowTargetSpacing*2)
            return nProofOfWorkLimit;
    }

    int T = params.nPowTargetSpacing;   // 600
    int N = params.nJacobEmaAveragingWindow;   // 50

    int limit = std::min(7, std::max((N * 100 / 89) - N, 10));

    // Find the max timestamp within last `limit` blocks.
    int height_first = pindexLast->nHeight - limit + 1;
    assert(height_first >= 0);
    int64_t max_time = 0;
    for (int i = height_first; i < pindexLast->nHeight; ++i) {
        int64_t block_time = pindexLast->GetAncestor(i)->GetBlockTime();
        if (block_time > max_time) {
            max_time = block_time;
        }
    }

    uint64_t solve_time = pindexLast->GetBlockTime() - max_time;   // ~600
    solve_time = std::max((uint64_t)(T / 200), std::min((uint64_t)(T * limit), solve_time));  // 200???? 3?
    uint32_t previous_target = pindexLast->nBits;

    return JacobEmaCalculateNextWorkRequired(T, N , solve_time, previous_target);
}

unsigned int JacobEmaCalculateNextWorkRequired(int T, int N, uint64_t solve_time_u64, uint32_t previous_target)
{
    // This function implements a deterministic version of Jacob's EMA algorithm:
    //    diff = prev_diff * (T / ST + exp(-2 * ST / (T * N)) * (1 - T / ST))
    // which is equivelant to:
    //    target = prev_target * ST / ((ST - T) * exp(-2 * ST / (T * N)) - T)
    //
    // It uses 256-bits fixed point to represent real number in a deterministic way.
    // Variables prefixed by "f128" means the base is 2^128, while "f192" means the base is 2^192.
    // E.g.
    //            x == 0x1122
    //       f128_x == 0x1122 << 128
    //       f192_x == 0x1122 << 192

    static const int TARGET_SHIFT = 192;
    static const int FIXED_SHIFT = 128;

    arith_uint256 solve_time(solve_time_u64);

    // Convert the compact target to magnifier (target_size) and value (prev_target_value).
    // (Assume previous_target is a positive number)
    uint32_t target_size = (previous_target >> 24) & 0xFF;
    arith_uint256 prev_target_value = previous_target & 0x7FFFFF;
    // Use base 2^192 fixed point to ensure the precision when divided by a base 2^128 number later.
    arith_uint256 f192_prev_target = prev_target_value << TARGET_SHIFT;

    // exp_result = exp(-2 * ST / (T * N))
    arith_uint256 f128_exp = (solve_time << 128) * 2 / (T * N);
    arith_uint256 f128_exp_result = f128_neg_exp(f128_exp);

    // den = (ST - T) * exp_r + T
    arith_uint256 f128_den = (solve_time - T) * f128_exp_result + (arith_uint256(T) << 128);
    // target = prev_target * ST / den
    arith_uint256 target = (f192_prev_target * solve_time / f128_den) >> (TARGET_SHIFT - FIXED_SHIFT);

    // Apply the magnifier from the previous target:
    //   target = target * 2^(8 * (magnifier - 3))
    if (target_size <= 3) {
        target >>= (8 * (3 - target_size));
    } else {
        target <<= (8 * (target_size - 3));
    }
    uint32_t result = target.GetCompact();
    return result;
}

arith_uint256 f128_neg_exp(arith_uint256 f128_x, int n)
{
    // Calculate exp(-x) in 256-bits fixed point with 2^128 base by Tylor series:
    //     exp(-x) = 1 - x * (1 - x/2 * (1 - x/3 * ( ... * (1 - x/n) )))
    static const arith_uint256 f128_1 = arith_uint256(1) << 128;
    arith_uint256 f128_result = f128_1;
    while(n > 0){
        f128_result = (f128_1 - f128_x * f128_result / n) >> 128;
        n--;
    }
    return f128_result;
}

unsigned int DigishieldGetNextWorkRequired(const CBlockIndex* pindexLast, const CBlockHeader *pblock,
                                           const Consensus::Params& params)
{
    assert(pindexLast != nullptr);
    if (params.fPowNoRetargeting)
        return pindexLast->nBits;
    unsigned int nProofOfWorkLimit = UintToArith256(params.PowLimit(true)).GetCompact();  // Always postfork.

    const CBlockIndex* pindexFirst = pindexLast;
    arith_uint256 bnTot {0};
    for (int i = 0; pindexFirst && i < params.nDigishieldAveragingWindow; i++) {
        arith_uint256 bnTmp;
        bnTmp.SetCompact(pindexFirst->nBits);
        bnTot += bnTmp;
        pindexFirst = pindexFirst->pprev;
    }
    
    if (pindexFirst == NULL)
        return nProofOfWorkLimit;
    
    arith_uint256 bnAvg {bnTot / params.nDigishieldAveragingWindow};
    return DigishieldCalculateNextWorkRequired(bnAvg, pindexLast->GetMedianTimePast(), pindexFirst->GetMedianTimePast(),
                                               params);
}

unsigned int DigishieldCalculateNextWorkRequired(arith_uint256 bnAvg, int64_t nLastBlockTime, int64_t nFirstBlockTime,
                                                 const Consensus::Params& params)
{
    // Limit adjustment
    int64_t nActualTimespan = nLastBlockTime - nFirstBlockTime;
    
    if (nActualTimespan < params.DigishieldMinActualTimespan())
        nActualTimespan = params.DigishieldMinActualTimespan();
    if (nActualTimespan > params.DigishieldMaxActualTimespan())
        nActualTimespan = params.DigishieldMaxActualTimespan();

    // Retarget
    const arith_uint256 bnPowLimit = UintToArith256(params.PowLimit(true));
    arith_uint256 bnNew {bnAvg};
    bnNew /= params.DigishieldAveragingWindowTimespan();
    bnNew *= nActualTimespan;
    
    if (bnNew > bnPowLimit)
        bnNew = bnPowLimit;

    return bnNew.GetCompact();
}

unsigned int BitcoinGetNextWorkRequired(const CBlockIndex* pindexLast, const CBlockHeader *pblock, const Consensus::Params& params)
{
    assert(pindexLast != nullptr);
    unsigned int nProofOfWorkLimit = UintToArith256(params.PowLimit(false)).GetCompact();
    
    // Only change once per difficulty adjustment interval
    if ((pindexLast->nHeight+1) % params.DifficultyAdjustmentInterval() != 0)
    {
        if (params.fPowAllowMinDifficultyBlocks)
        {
            // Special difficulty rule for testnet:
            // If the new block's timestamp is more than 2* 10 minutes
            // then allow mining of a min-difficulty block.
            if (pblock->GetBlockTime() > pindexLast->GetBlockTime() + params.nPowTargetSpacing*2)
                return nProofOfWorkLimit;
            else
            {
                // Return the last non-special-min-difficulty-rules-block
                const CBlockIndex* pindex = pindexLast;
                while (pindex->pprev && pindex->nHeight % params.DifficultyAdjustmentInterval() != 0 && pindex->nBits == nProofOfWorkLimit)
                    pindex = pindex->pprev;
                return pindex->nBits;
            }
        }
        return pindexLast->nBits;
    }

    // Go back by what we want to be 14 days worth of blocks
    int nHeightFirst = pindexLast->nHeight - (params.DifficultyAdjustmentInterval()-1);
    assert(nHeightFirst >= 0);
    const CBlockIndex* pindexFirst = pindexLast->GetAncestor(nHeightFirst);
    assert(pindexFirst);

    return BitcoinCalculateNextWorkRequired(pindexLast, pindexFirst->GetBlockTime(), params);
}

unsigned int BitcoinCalculateNextWorkRequired(const CBlockIndex* pindexLast, int64_t nFirstBlockTime, const Consensus::Params& params)
{
    if (params.fPowNoRetargeting)
        return pindexLast->nBits;
    
    // Limit adjustment step
    int64_t nActualTimespan = pindexLast->GetBlockTime() - nFirstBlockTime;
    if (nActualTimespan < params.nPowTargetTimespanLegacy/4)
        nActualTimespan = params.nPowTargetTimespanLegacy/4;
    if (nActualTimespan > params.nPowTargetTimespanLegacy*4)
        nActualTimespan = params.nPowTargetTimespanLegacy*4;
    
    // Retarget
    const arith_uint256 bnPowLimit = UintToArith256(params.PowLimit(false));
    arith_uint256 bnNew;
    bnNew.SetCompact(pindexLast->nBits);
    bnNew *= nActualTimespan;
    bnNew /= params.nPowTargetTimespanLegacy;
    
    if (bnNew > bnPowLimit)
        bnNew = bnPowLimit;
    
    return bnNew.GetCompact();
}

bool CheckEquihashSolution(const CBlockHeader *pblock, const CChainParams& params)
{
    unsigned int n = params.EquihashN();
    unsigned int k = params.EquihashK();

    // Hash state
    crypto_generichash_blake2b_state state;
    EhInitialiseState(n, k, state);

    // I = the block header minus nonce and solution.
    CEquihashInput I{*pblock};
    // I||V
    CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
    ss << I;
    ss << pblock->nNonce;

    // H(I||V||...
    crypto_generichash_blake2b_update(&state, (unsigned char*)&ss[0], ss.size());

    bool isValid;
    EhIsValidSolution(n, k, state, pblock->nSolution, isValid);
    if (!isValid)
        return error("CheckEquihashSolution(): invalid solution");

    return true;
}

bool CheckProofOfWork(uint256 hash, unsigned int nBits, bool postfork, const Consensus::Params& params)
{
    bool fNegative;
    bool fOverflow;
    arith_uint256 bnTarget;

    bnTarget.SetCompact(nBits, &fNegative, &fOverflow);

    // Check range
    if (fNegative || bnTarget == 0 || fOverflow || bnTarget > UintToArith256(params.PowLimit(postfork)))
        return false;

    // Check proof of work matches claimed amount
    if (UintToArith256(hash) > bnTarget)
        return false;

    return true;
}
