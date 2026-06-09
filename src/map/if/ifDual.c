/**CFile****************************************************************

  FileName    [ifDual.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Strict-depth and dual-output LUT mapping support.]

***********************************************************************/

#include "if.h"
#include "base/abc/abc.h"
#include "misc/util/abc_global.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int       If_DualDepth( If_Man_t * p, float Delay );
static If_Cand_t * If_DualCandAlloc( If_Man_t * p, int Depth, If_Cut_t * pCut, float AreaFlow );
static If_Cand_t * If_DualSelectCand( If_Man_t * p, If_Obj_t * pObj, int DepthLimit );
static int       If_DualObjHasCandAtLimit( If_Man_t * p, If_Obj_t * pObj, int DepthLimit );
static If_DualPair_t * If_DualFindPair( If_Man_t * p, If_Obj_t * pObj );
static int       If_DualObjLevel( If_Man_t * p, Vec_Int_t * vLevels, If_Obj_t * pObj );
static int       If_DualCutOutputLevel( If_Man_t * p, Vec_Int_t * vLevels, If_Obj_t * pObj, If_Cut_t * pCut, If_Obj_t * pMate, If_Cut_t * pMateCut );

/* 把 ABC clock tick 转成秒，用于 strict/dual 内部耗时日志。 */
static double If_DualTimeSec( abctime Time )
{
    return 1.0 * (double)Time / (double)CLOCKS_PER_SEC;
}

/* best-cover score 的默认权重：只惩罚归一化 LUT 面积和 depth。 */
static double If_DualScoreMu( void )     { return 2.00; }

////////////////////////////////////////////////////////////////////////
///                     CANDIDATE STORAGE                            ///
////////////////////////////////////////////////////////////////////////

/* 将 IF 的浮点 delay 转成整数 LUT 层数，用 epsilon 处理浮点误差。 */
static int If_DualDepth( If_Man_t * p, float Delay )
{
    int Depth = (int)Delay;
    if ( Delay > (float)Depth + p->fEpsilon )
        Depth++;
    return Depth;
}

/* 为一个枚举 cut 分配候选记录，并把变长 If_Cut_t 完整拷贝进去。 */
static If_Cand_t * If_DualCandAlloc( If_Man_t * p, int Depth, If_Cut_t * pCut, float AreaFlow )
{
    int nBytes = (int)(sizeof(If_Cand_t) - sizeof(If_Cut_t)) + p->nCutBytes;
    If_Cand_t * pCand = (If_Cand_t *)ABC_ALLOC( char, nBytes );
    memset( pCand, 0, (size_t)nBytes );
    pCand->Depth = Depth;
    pCand->Size  = pCut->nLeaves;
    pCand->Area  = AreaFlow;
    If_CutCopy( p, &pCand->Cut, pCut );
    pCand->Cut.Area = AreaFlow;
    return pCand;
}

/* 释放单个 IF 对象上的 strict/dual 临时状态和候选 cut 集合。 */
void If_DualFreeObj( If_Man_t * p, If_Obj_t * pObj )
{
    If_Cand_t * pCand;
    int i;
    if ( pObj->vIfBestCuts )
    {
        Vec_PtrForEachEntry( If_Cand_t *, pObj->vIfBestCuts, pCand, i )
            ABC_FREE( pCand );
        Vec_PtrFree( pObj->vIfBestCuts );
        pObj->vIfBestCuts = NULL;
    }
    pObj->pIfDualMate = NULL;
    pObj->pIfCandBest = NULL;
    pObj->fIfMapped = 0;
    pObj->fIfLocked = 0;
    pObj->fIfDualRoot = 0;
    pObj->IfDepthLimit = IF_INFINITY;
    pObj->IfCandMinDepth = IF_INFINITY;
    (void)p;
}

/* 清空整个 IF manager 的 strict/dual 数据，用于重新开始一次搜索。 */
void If_DualClearAll( If_Man_t * p )
{
    If_Obj_t * pObj;
    If_DualPair_t * pPair;
    int i;
    If_ManForEachObj( p, pObj, i )
        If_DualFreeObj( p, pObj );
    if ( p->vIfDualPairs )
    {
        Vec_PtrForEachEntry( If_DualPair_t *, p->vIfDualPairs, pPair, i )
            ABC_FREE( pPair );
        Vec_PtrFree( p->vIfDualPairs );
        p->vIfDualPairs = NULL;
    }
    Vec_PtrFreeP( &p->vIfMappedSingles );
    p->fIfStrictCollect = 0;
    p->nIfStrictMaxDepth = 0;
}

/* 只重置一次 BWD cover/dual pairing 的状态，保留 FWD 候选表。 */
static void If_DualResetCoverState( If_Man_t * p )
{
    If_Obj_t * pObj;
    If_DualPair_t * pPair;
    int i;
    If_ManForEachObj( p, pObj, i )
    {
        pObj->pIfDualMate = NULL;
        pObj->pIfCandBest = NULL;
        pObj->fIfMapped = 0;
        pObj->fIfLocked = 0;
        pObj->fIfDualRoot = 0;
        pObj->IfDepthLimit = IF_INFINITY;
    }
    if ( p->vIfDualPairs )
    {
        Vec_PtrForEachEntry( If_DualPair_t *, p->vIfDualPairs, pPair, i )
            ABC_FREE( pPair );
        Vec_PtrClear( p->vIfDualPairs );
    }
    else
        p->vIfDualPairs = Vec_PtrAlloc( 100 );
    if ( p->vIfMappedSingles )
        Vec_PtrClear( p->vIfMappedSingles );
    else
        p->vIfMappedSingles = Vec_PtrAlloc( 1000 );
}

/* 从普通 IF cut 枚举流程中记录候选：每个 depth/size 桶保留最低 AF cut。 */
void If_DualRecordCandidate( If_Man_t * p, If_Obj_t * pObj, If_Cut_t * pCut )
{
    If_Cand_t * pCand, * pCandNew;
    float AreaFlow;
    int i, Depth, iInsert;
    if ( !p->fIfStrictCollect || pCut->fUseless )
        return;
    Depth = If_DualDepth( p, pCut->Delay );
    /* Strict collection is intentionally global-depth based.  Local required
       times are not used here because the outer loop is exploring relaxed
       max-level budgets beyond the classic IF baseline. */
    if ( Depth > p->nIfStrictMaxDepth || pCut->nLeaves > (unsigned)p->pPars->nLutSize )
        return;
    AreaFlow = If_CutAreaFlow( p, pCut );
    if ( pObj->vIfBestCuts == NULL )
    {
        pObj->vIfBestCuts = Vec_PtrAlloc( p->pPars->nLutSize * 4 );
        pObj->IfCandMinDepth = IF_INFINITY;
    }
    pObj->IfCandMinDepth = Abc_MinInt( pObj->IfCandMinDepth, Depth );
    /* Called from the normal cut evaluator for every enumerated cut.
       Each (output depth, cut size) bucket keeps only the lowest AF cut. */
    Vec_PtrForEachEntry( If_Cand_t *, pObj->vIfBestCuts, pCand, i )
    {
        if ( pCand->Depth != Depth || pCand->Size != (int)pCut->nLeaves )
            continue;
        if ( AreaFlow + p->fEpsilon < pCand->Area )
        {
            pCand->Area = AreaFlow;
            If_CutCopy( p, &pCand->Cut, pCut );
            pCand->Cut.Area = AreaFlow;
        }
        return;
    }
    pCandNew = If_DualCandAlloc( p, Depth, pCut, AreaFlow );
    /* Keep candidates sorted by depth while preserving original order inside
       the same depth.  BWD selection can then stop once depth exceeds limit. */
    Vec_PtrForEachEntry( If_Cand_t *, pObj->vIfBestCuts, pCand, iInsert )
        if ( pCand->Depth > Depth )
            break;
    if ( iInsert == Vec_PtrSize(pObj->vIfBestCuts) )
        Vec_PtrPush( pObj->vIfBestCuts, pCandNew );
    else
        Vec_PtrInsert( pObj->vIfBestCuts, iInsert, pCandNew );
}

/* 判断一个对象在给定剩余 depth limit 内是否存在可用候选 cut。 */
static int If_DualObjHasCandAtLimit( If_Man_t * p, If_Obj_t * pObj, int DepthLimit )
{
    if ( If_ObjIsCi(pObj) || If_ObjIsConst1(pObj) )
        return DepthLimit >= 0;
    /* Non-terminals must be realizable by one LUT level plus their leaves,
       so depth 0 cannot satisfy an internal node. */
    if ( DepthLimit < 1 || pObj->vIfBestCuts == NULL )
        return 0;
    return pObj->IfCandMinDepth <= DepthLimit;
}

/* 检查某个 cut 的所有叶子是否都能在 DepthLimit-1 内继续被 cover。 */
static int If_DualCutLeavesHaveSlack( If_Man_t * p, If_Cut_t * pCut, int DepthLimit )
{
    If_Obj_t * pLeaf;
    int i;
    /* Candidate tables are already depth-closed by FWD DP, so one leaf lookup
       is enough; recursive feasibility checks would only repeat this work. */
    If_CutForEachLeaf( p, pCut, pLeaf, i )
        if ( !If_DualObjHasCandAtLimit( p, pLeaf, DepthLimit - 1 ) )
            return 0;
    return 1;
}

/* 在一个节点的所有候选中，选择满足 depth limit 且 AF 最低的 single-LUT cut。 */
static If_Cand_t * If_DualSelectCand( If_Man_t * p, If_Obj_t * pObj, int DepthLimit )
{
    If_Cand_t * pCand, * pBest = NULL;
    int i;
    if ( If_ObjIsCi(pObj) || If_ObjIsConst1(pObj) || pObj->vIfBestCuts == NULL )
        return NULL;
    Vec_PtrForEachEntry( If_Cand_t *, pObj->vIfBestCuts, pCand, i )
    {
        /* The BWD cover chooses among all saved depth/size buckets, not only
           the classic CutBest bucket.  This is where extra merge opportunities
           from non-best-sized cuts are allowed back into the cover. */
        if ( pCand->Depth > DepthLimit )
            break;
        if ( !If_DualCutLeavesHaveSlack( p, &pCand->Cut, DepthLimit ) )
            continue;
        if ( pBest == NULL || pCand->Area < pBest->Area - p->fEpsilon ||
             (pCand->Area < pBest->Area + p->fEpsilon && pCand->Depth < pBest->Depth) )
            pBest = pCand;
    }
    return pBest;
}

/* cover 失败时打印单个节点的候选摘要，辅助定位候选缺失/limit 过紧。 */
static void If_DualPrintCandSummary( If_Man_t * p, If_Obj_t * pObj, int DepthLimit )
{
    If_Cand_t * pCand;
    int i;
    Abc_Print( 1, "    If-debug obj=%d limit=%d cands=%d", pObj->Id, DepthLimit,
        pObj->vIfBestCuts ? Vec_PtrSize(pObj->vIfBestCuts) : 0 );
    if ( pObj->vIfBestCuts )
        Vec_PtrForEachEntry( If_Cand_t *, pObj->vIfBestCuts, pCand, i )
            Abc_Print( 1, " [d=%d s=%d af=%.2f]", pCand->Depth, pCand->Size, pCand->Area );
    Abc_Print( 1, "\n" );
    (void)p;
}

////////////////////////////////////////////////////////////////////////
///                     DUAL WINDOW CHECKING                         ///
////////////////////////////////////////////////////////////////////////

/* 向 dual window leaf 数组加入一个对象 ID，保持去重；超过 limit 时提前失败。 */
static int If_DualPushLeafUnique( int * pLeaves, int * pnLeaves, int ObjId, int Limit )
{
    int i;
    for ( i = 0; i < *pnLeaves; i++ )
        if ( pLeaves[i] == ObjId )
            return 1;
    if ( *pnLeaves >= Limit )
        return 0;
    pLeaves[(*pnLeaves)++] = ObjId;
    return 1;
}

/* 对 dual window leaf 数组排序，保证属性传递和 Verilog 输出稳定。 */
static void If_DualSortLeaves( int * pLeaves, int nLeaves )
{
    int i, k;
    for ( i = 0; i < nLeaves; i++ )
        for ( k = i + 1; k < nLeaves; k++ )
            if ( pLeaves[i] > pLeaves[k] )
                ABC_SWAP( int, pLeaves[i], pLeaves[k] );
}

/* 加入一个 cut 的 leaves；若 leaf 是另一个输出 root，则展开成该 root 的 cut leaves。 */
static int If_DualAddExpandedCutLeaves( If_Cut_t * pCut, int OtherRoot, If_Cut_t * pOtherCut, int * pLeaves, int * pnLeaves, int Limit )
{
    int i, k;
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
    {
        if ( pCut->pLeaves[i] == OtherRoot )
        {
            for ( k = 0; k < (int)pOtherCut->nLeaves; k++ )
                if ( !If_DualPushLeafUnique( pLeaves, pnLeaves, pOtherCut->pLeaves[k], Limit ) )
                    return 0;
        }
        else if ( !If_DualPushLeafUnique( pLeaves, pnLeaves, pCut->pLeaves[i], Limit ) )
            return 0;
    }
    return 1;
}

/* 合并两个 cut 的物理输入集合；串联时把内部输出 root 展开为它自己的 leaves。 */
static int If_DualMergeLeaves( If_Obj_t * pObj0, If_Cut_t * pCut0, If_Obj_t * pObj1, If_Cut_t * pCut1, int * pLeaves, int Limit )
{
    int nLeaves = 0;
    if ( !If_DualAddExpandedCutLeaves( pCut0, pObj1->Id, pCut1, pLeaves, &nLeaves, Limit ) )
        return Limit + 1;
    if ( !If_DualAddExpandedCutLeaves( pCut1, pObj0->Id, pCut0, pLeaves, &nLeaves, Limit ) )
        return Limit + 1;
    If_DualSortLeaves( pLeaves, nLeaves );
    return nLeaves;
}

/* 估算 dual window 的面积流：一个 dual LUT 面积加上 union leaves 的摊销 AF。 */
static float If_DualWindowAreaFlow( If_Man_t * p, If_Cut_t * pCut0, If_Cut_t * pCut1, int * pLeaves, int nLeaves )
{
    If_Obj_t * pLeaf;
    float Flow, AddOn;
    int i;
    (void)pCut0;
    (void)pCut1;
    Flow = p->pPars->pLutLib ? p->pPars->pLutLib->pLutAreas[p->pPars->nLutSize] : (float)1.0;
    for ( i = 0; i < nLeaves; i++ )
    {
        pLeaf = If_ManObj( p, pLeaves[i] );
        if ( pLeaf->nRefs == 0 || If_ObjIsConst1(pLeaf) )
            AddOn = If_ObjCutBest(pLeaf)->Area;
        else
        {
            /* Relaxed-depth collection skips some original ref side effects.
               If EstRefs is unavailable, divide by one rather than rejecting
               a legal dual window with a debug-only assertion. */
            float EstRefs = Abc_MaxFloat( pLeaf->EstRefs, (float)1.0 );
            AddOn = If_ObjCutBest(pLeaf)->Area / EstRefs;
        }
        Flow = Flow >= (float)1e32 || AddOn >= (float)1e32 ? (float)1e32 : Flow + AddOn;
    }
    return Flow;
}

/* 检查两个 single cut 是否能形成简单 dual window，并返回展开后的 union leaves/AF。 */
static int If_DualWindowFeasible( If_Man_t * p, If_Obj_t * pObj0, If_Cut_t * pCut0, int Limit0, If_Obj_t * pObj1, If_Cut_t * pCut1, int Limit1, float * pWindowFlow, int * pLeaves, int * pnLeaves )
{
    int nLeaves = If_DualMergeLeaves( pObj0, pCut0, pObj1, pCut1, pLeaves, p->pPars->nLutSize - 1 );
    /* This implements only the requested simple case: two LUT outputs share
       one physical dual-LUT input set of at most N-1 data leaves. */
    if ( nLeaves > p->pPars->nLutSize - 1 )
        return 0;
    *pWindowFlow = If_DualWindowAreaFlow( p, pCut0, pCut1, pLeaves, nLeaves );
    if ( *pWindowFlow > pCut0->Area + pCut1->Area + p->fEpsilon )
        return 0;
    /* 两个 cut 都已经是 BWD single cover 选出的 CutBest，因此其 leaves 在各自
       root 的 depth limit 下已经通过 slack 检查；公共 leaf 也自然满足更紧的
       limit。这里不再重复 candidate 查询，只把 size/AF 作为 window 过滤条件。 */
    (void)Limit0;
    (void)Limit1;
    *pnLeaves = nLeaves;
    return 1;
}

/* 判断 cut 的第 i 个 leaf 是否真的影响该 cut 的输出；truth 缺失时保守认为依赖。 */
static int If_DualCutLeafDepends( If_Man_t * p, If_Cut_t * pCut, int iLeaf )
{
    word * pTruth;
    if ( iLeaf < 0 || iLeaf >= (int)pCut->nLeaves )
        return 0;
    if ( !p->pPars->fTruth || pCut->iCutFunc < 0 || p->vTtMem[pCut->nLeaves] == NULL )
        return 1;
    pTruth = If_CutTruthW( p, pCut );
    return pTruth == NULL ? 1 : Abc_TtHasVar( pTruth, pCut->nLeaves, iLeaf );
}

/* 计算一个 single/dual 输出的真实逻辑层级。若 cut 里出现 mate 输出，
   说明是串联合并，需要把这个 mate 输出展开成它自己的真实支持集合。 */
static int If_DualCutOutputLevel( If_Man_t * p, Vec_Int_t * vLevels, If_Obj_t * pObj, If_Cut_t * pCut, If_Obj_t * pMate, If_Cut_t * pMateCut )
{
    int i, k, Level = 0;
    for ( i = 0; i < (int)pCut->nLeaves; i++ )
    {
        if ( !If_DualCutLeafDepends( p, pCut, i ) )
            continue;
        if ( pMate && pCut->pLeaves[i] == pMate->Id )
        {
            for ( k = 0; k < (int)pMateCut->nLeaves; k++ )
            {
                if ( !If_DualCutLeafDepends( p, pMateCut, k ) )
                    continue;
                if ( pMateCut->pLeaves[k] == pObj->Id )
                    return IF_INFINITY;
                Level = Abc_MaxInt( Level, Vec_IntEntry(vLevels, pMateCut->pLeaves[k]) );
            }
        }
        else
            Level = Abc_MaxInt( Level, Vec_IntEntry(vLevels, pCut->pLeaves[i]) );
    }
    return Level + 1;
}

/* 分别计算 dual window 两个输出的层级；不是所有 union leaf 都一定影响两个输出。 */
static void If_DualWindowLevels( If_Man_t * p, Vec_Int_t * vLevels, If_Obj_t * pObj0, If_Cut_t * pCut0, If_Obj_t * pObj1, If_Cut_t * pCut1, int * pLevel0, int * pLevel1 )
{
    *pLevel0 = If_DualCutOutputLevel( p, vLevels, pObj0, pCut0, pObj1, pCut1 );
    *pLevel1 = If_DualCutOutputLevel( p, vLevels, pObj1, pCut1, pObj0, pCut0 );
}

/* 重新计算当前 single/dual cover 的 PO 最大物理层级，用于验证一次新 pair
   是否会通过下游 fanout 把全局 depth 顶过本轮限制。 */
static int If_DualComputeCoverDepth( If_Man_t * p )
{
    Vec_Int_t * vLevels = Vec_IntStart( If_ManObjNum(p) );
    If_Obj_t * pObj;
    int i, Depth = 0;
    If_ManForEachObj( p, pObj, i )
        Vec_IntWriteEntry( vLevels, pObj->Id, If_DualObjLevel(p, vLevels, pObj) );
    If_ManForEachCo( p, pObj, i )
        Depth = Abc_MaxInt( Depth, Vec_IntEntry(vLevels, If_ObjFanin0(pObj)->Id) );
    Vec_IntFree( vLevels );
    return Depth;
}

/* 接受一个 dual pair，记录 pair 元数据并锁定两个输出节点。 */
static void If_DualAddPair( If_Man_t * p, If_Obj_t * pObj0, If_Obj_t * pObj1, int * pLeaves, int nLeaves )
{
    If_DualPair_t * pPair = ABC_CALLOC( If_DualPair_t, 1 );
    int i;
    pPair->Obj0 = pObj0->Id;
    pPair->Obj1 = pObj1->Id;
    pPair->nLeaves = nLeaves;
    for ( i = 0; i < nLeaves; i++ )
        pPair->pLeaves[i] = pLeaves[i];
    Vec_PtrPush( p->vIfDualPairs, pPair );
    pObj0->pIfDualMate = pObj1;
    pObj1->pIfDualMate = pObj0;
    pObj0->fIfLocked = pObj1->fIfLocked = 1;
    pObj0->fIfDualRoot = 1;
    pObj1->fIfDualRoot = 0;
}

/* 撤销刚刚试探加入的最后一个 dual pair；只用于 depth guard 拒绝会破坏
   本轮严格深度的候选 pair，不参与跨迭代删除。 */
static void If_DualPopLastPair( If_Man_t * p, If_Obj_t * pObj0, If_Obj_t * pObj1 )
{
    If_DualPair_t * pPair;
    assert( p->vIfDualPairs && Vec_PtrSize(p->vIfDualPairs) > 0 );
    pPair = (If_DualPair_t *)Vec_PtrEntryLast( p->vIfDualPairs );
    ABC_FREE( pPair );
    Vec_PtrPop( p->vIfDualPairs );
    pObj0->pIfDualMate = NULL;
    pObj1->pIfDualMate = NULL;
    pObj0->fIfLocked = pObj1->fIfLocked = 0;
    pObj0->fIfDualRoot = pObj1->fIfDualRoot = 0;
}

/* 释放 dual pair 向量及其中的 pair 结构。 */
static void If_DualPairsFree( Vec_Ptr_t * vPairs )
{
    If_DualPair_t * pPair;
    int i;
    if ( vPairs == NULL )
        return;
    Vec_PtrForEachEntry( If_DualPair_t *, vPairs, pPair, i )
        ABC_FREE( pPair );
    Vec_PtrFree( vPairs );
}

/* 深拷贝 dual pair 列表，用于保存 best cover 快照。 */
static Vec_Ptr_t * If_DualPairsDup( Vec_Ptr_t * vPairs )
{
    Vec_Ptr_t * vCopy = Vec_PtrAlloc( vPairs ? Vec_PtrSize(vPairs) : 0 );
    If_DualPair_t * pPair, * pPairNew;
    int i;
    if ( vPairs == NULL )
        return vCopy;
    Vec_PtrForEachEntry( If_DualPair_t *, vPairs, pPair, i )
    {
        pPairNew = ABC_ALLOC( If_DualPair_t, 1 );
        memcpy( pPairNew, pPair, sizeof(If_DualPair_t) );
        Vec_PtrPush( vCopy, pPairNew );
    }
    return vCopy;
}

/* 根据某个输出节点查找它已经归属的 dual pair。 */
static If_DualPair_t * If_DualFindPair( If_Man_t * p, If_Obj_t * pObj )
{
    If_DualPair_t * pPair;
    int i;
    if ( p->vIfDualPairs == NULL )
        return NULL;
    Vec_PtrForEachEntry( If_DualPair_t *, p->vIfDualPairs, pPair, i )
        if ( pPair->Obj0 == pObj->Id || pPair->Obj1 == pObj->Id )
            return pPair;
    return NULL;
}

/* 在当前 single/dual cover 下计算一个 IF 对象的物理 LUT 层级。 */
static int If_DualObjLevel( If_Man_t * p, Vec_Int_t * vLevels, If_Obj_t * pObj )
{
    If_DualPair_t * pPair;
    If_Cut_t * pCut;
    if ( If_ObjIsCi(pObj) || If_ObjIsConst1(pObj) )
        return 0;
    pPair = pObj->fIfLocked ? If_DualFindPair( p, pObj ) : NULL;
    if ( pPair )
    {
        If_Obj_t * pObj0 = If_ManObj( p, pPair->Obj0 );
        If_Obj_t * pObj1 = If_ManObj( p, pPair->Obj1 );
        If_Obj_t * pMate = pObj->Id == pPair->Obj0 ? pObj1 : pObj0;
        return If_DualCutOutputLevel( p, vLevels, pObj, If_ObjCutBest(pObj), pMate, If_ObjCutBest(pMate) );
    }
    pCut = If_ObjCutBest( pObj );
    return If_DualCutOutputLevel( p, vLevels, pObj, pCut, NULL, NULL );
}

typedef struct If_DualStats_t_
{
    int Depth;
    int nSingles[IF_MAX_LUTSIZE+1];
    int nDual;
    int nTotal;
    int nEdges;
    double AreaNorm;
    double DepthNorm;
    double Score;
    int nCandObjs;
    int nCandTotal;
    int nCandMax;
} If_DualStats_t;

/* 判断 cover leaf 是否来自另一个 LUT/dual root，用于统计 LUT 间边数。 */
static int If_DualLeafIsInternalEdge( If_Man_t * p, int Leaf )
{
    If_Obj_t * pLeaf = If_ManObj( p, Leaf );
    return !If_ObjIsCi(pLeaf) && !If_ObjIsConst1(pLeaf);
}

/* 用用户给定的归一化公式计算 cover score：area_norm + mu * depth_norm。 */
static void If_DualUpdateScore( If_DualStats_t * pStats, int AreaBase, int DepthTarget )
{
    AreaBase = Abc_MaxInt( AreaBase, 1 );
    DepthTarget = Abc_MaxInt( DepthTarget, 1 );
    pStats->AreaNorm  = (double)pStats->nTotal / (double)AreaBase;
    pStats->DepthNorm = (double)pStats->Depth / (double)DepthTarget;
    pStats->Score = pStats->AreaNorm + If_DualScoreMu() * pStats->DepthNorm;
}

/* 统计当前 cover 的最大深度、single LUT 分布、dual 数量和候选规模。 */
static void If_DualCollectStats( If_Man_t * p, If_DualStats_t * pStats )
{
    Vec_Int_t * vLevels = Vec_IntStart( If_ManObjNum(p) );
    If_Obj_t * pObj;
    int i, nSingles = 0;
    memset( pStats, 0, sizeof(If_DualStats_t) );
    If_ManForEachObj( p, pObj, i )
        Vec_IntWriteEntry( vLevels, pObj->Id, If_DualObjLevel(p, vLevels, pObj) );
    If_ManForEachCo( p, pObj, i )
    {
        If_Obj_t * pDriver = If_ObjFanin0( pObj );
        pStats->Depth = Abc_MaxInt( pStats->Depth, Vec_IntEntry(vLevels, pDriver->Id) );
    }
    if ( p->vIfMappedSingles )
    {
        Vec_PtrForEachEntry( If_Obj_t *, p->vIfMappedSingles, pObj, i )
        {
            If_Cut_t * pCut;
            int Size, k;
            if ( pObj->fIfLocked )
                continue;
            pCut = If_ObjCutBest(pObj);
            Size = Abc_MaxInt( 1, (int)pCut->nLeaves );
            Size = Abc_MinInt( Size, IF_MAX_LUTSIZE );
            pStats->nSingles[Size]++;
            for ( k = 0; k < (int)pCut->nLeaves; k++ )
                pStats->nEdges += If_DualLeafIsInternalEdge( p, pCut->pLeaves[k] );
            nSingles++;
        }
    } 
    if ( p->vIfDualPairs )
    {
        If_DualPair_t * pPair;
        Vec_PtrForEachEntry( If_DualPair_t *, p->vIfDualPairs, pPair, i )
        {
            int k;
            for ( k = 0; k < pPair->nLeaves; k++ )
                pStats->nEdges += If_DualLeafIsInternalEdge( p, pPair->pLeaves[k] );
        }
    }
    If_ManForEachObj( p, pObj, i )
        if ( pObj->vIfBestCuts )
        {
            pStats->nCandObjs++;
            pStats->nCandTotal += Vec_PtrSize( pObj->vIfBestCuts );
            pStats->nCandMax = Abc_MaxInt( pStats->nCandMax, Vec_PtrSize(pObj->vIfBestCuts) );
        }
    pStats->nDual = p->vIfDualPairs ? Vec_PtrSize(p->vIfDualPairs) : 0;
    pStats->nTotal = nSingles + pStats->nDual;
    Vec_IntFree( vLevels );
}

/* 按统一格式打印一轮 seed/iter/best cover 的统计日志。 */
static void If_DualPrintStats( If_Man_t * p, int DepthLimit, char * pTag, If_DualStats_t * pStats )
{
    int k;
    Abc_Print( 1, "    If-%s depth_limit=%d max_depth=%d ", pTag, DepthLimit, pStats->Depth );
    for ( k = 1; k <= p->pPars->nLutSize; k++ )
        Abc_Print( 1, "LUT%d=%d ", k, pStats->nSingles[k] );
    Abc_Print( 1, "dual_lut%d=%d total_luts=%d edges=%d norm_area=%.3f norm_depth=%.3f score=%.3f cand_objs=%d cand_total=%d cand_avg=%.2f cand_max=%d\n",
        p->pPars->nLutSize, pStats->nDual, pStats->nTotal, pStats->nEdges,
        pStats->AreaNorm, pStats->DepthNorm, pStats->Score,
        pStats->nCandObjs, pStats->nCandTotal,
        pStats->nCandObjs ? (double)pStats->nCandTotal / pStats->nCandObjs : 0.0,
        pStats->nCandMax );
}

////////////////////////////////////////////////////////////////////////
///                     BACKWARD COVER                                ///
////////////////////////////////////////////////////////////////////////

/* 将 BWD cover 任务入队；同一节点重复入队时保留更紧的 depth limit。 */
static int If_DualEnqueue( If_Man_t * p, Vec_Int_t * vQueue, If_Obj_t * pObj, int DepthLimit )
{
    if ( If_ObjIsCi(pObj) || If_ObjIsConst1(pObj) )
        return DepthLimit >= 0;
    if ( DepthLimit < 1 )
    {
        Abc_Print( 1, "    If-debug enqueue failed obj=%d limit=%d\n", pObj->Id, DepthLimit );
        return 0;
    }
    if ( pObj->IfDepthLimit <= DepthLimit )
        return 1;
    pObj->IfDepthLimit = DepthLimit;
    Vec_IntPushTwo( vQueue, pObj->Id, DepthLimit );
    return 1;
}

/* 从 PO 反向生成 single-LUT cover，并沿 cut leaves 传播剩余 depth limit。 */
static int If_DualCoverSingles( If_Man_t * p, int DepthLimit )
{
    Vec_Int_t * vQueue = Vec_IntAlloc( 1000 );
    If_Obj_t * pCo, * pObj, * pLeaf; 
    If_Cand_t * pCand;
    int i, k, ObjId, Limit;
    If_ManForEachCo( p, pCo, i )
        /* Queue payload is (object id, remaining depth).  If a node is reached
           through several POs, If_DualEnqueue keeps the tightest limit. */
        if ( !If_DualEnqueue( p, vQueue, If_ObjFanin0(pCo), DepthLimit ) )
        {
            Vec_IntFree( vQueue );
            return 0;
        }
    for ( i = 0; i < Vec_IntSize(vQueue); i += 2 ) 
    {
        ObjId = Vec_IntEntry( vQueue, i );
        Limit = Vec_IntEntry( vQueue, i + 1 );
        pObj = If_ManObj( p, ObjId );
        if ( Limit != pObj->IfDepthLimit )
            continue;
        pCand = If_DualSelectCand( p, pObj, Limit );
        if ( pCand == NULL )
        {
            If_DualPrintCandSummary( p, pObj, Limit );
            Vec_IntFree( vQueue );
            return 0;
        }
        If_CutCopy( p, If_ObjCutBest(pObj), &pCand->Cut );
        pObj->pIfCandBest = pCand;
        pObj->fIfMapped = 1;
        /* BWD propagation stores the tightest remaining depth directly on the
           queued node; stale queue entries are skipped when a tighter one wins. */
        If_CutForEachLeaf( p, If_ObjCutBest(pObj), pLeaf, k )
            if ( !If_DualEnqueue( p, vQueue, pLeaf, Limit - 1 ) )
            {
                Vec_IntFree( vQueue );
                return 0;
            }
    }
    Vec_IntFree( vQueue );
    return 1;
}

/* 从 PO 标记当前 CutBest 可达节点，再按 IF 拓扑顺序重建 mapped single roots。
   dual pairing 需要从 PI 侧走向 PO 侧；否则先合并 fanout、后合并 fanin 时，
   fanin level 的后续升高会让已经接受的 fanout window 事后超出 depth limit。 */
static void If_DualRebuildMappedSingles( If_Man_t * p )
{
    Vec_Int_t * vStack = Vec_IntAlloc( 1000 );
    If_Obj_t * pObj, * pCo, * pLeaf;
    int i, k, ObjId;
    Vec_PtrClear( p->vIfMappedSingles );
    If_ManForEachObj( p, pObj, i )
        pObj->fIfMapped = 0;
    /* The queue cover may have visited nodes that are no longer reachable after
       tighter limits replace looser ones.  Rebuild from POs before pairing. */
    If_ManForEachCo( p, pCo, i )
        Vec_IntPush( vStack, If_ObjFanin0(pCo)->Id );
    while ( Vec_IntSize(vStack) )
    {
        ObjId = Vec_IntEntryLast( vStack );
        Vec_IntPop( vStack );
        pObj = If_ManObj( p, ObjId );
        if ( If_ObjIsCi(pObj) || If_ObjIsConst1(pObj) || pObj->fIfMapped )
            continue;
        pObj->fIfMapped = 1;
        Vec_PtrPush( p->vIfMappedSingles, pObj );
        If_CutForEachLeaf( p, If_ObjCutBest(pObj), pLeaf, k )
            Vec_IntPush( vStack, pLeaf->Id );
    }
    Vec_PtrClear( p->vIfMappedSingles );
    If_ManForEachObj( p, pObj, i )
        if ( pObj->fIfMapped )
            Vec_PtrPush( p->vIfMappedSingles, pObj );
    Vec_IntFree( vStack );
}

/* 尝试把当前 single LUT 与一个未锁定 single LUT 贪心合并为 dual LUT。 */
static int If_DualTryMerge( If_Man_t * p, Vec_Int_t * vLevels, If_Obj_t * pObj, int DepthLimit, int * pnRejected )
{
    If_Obj_t * pMate, * pBestMate = NULL;
    float BestSaving = 0.0, WindowFlow, BestFlow = 0.0;
    int i, Leaves[IF_MAX_LUTSIZE], BestLeaves[IF_MAX_LUTSIZE], nLeaves = 0, nBestLeaves = 0, Level0, Level1, BestLevel0 = 0, BestLevel1 = 0;
    if ( !p->pPars->fDualOutput || pObj->fIfLocked || If_ObjCutBest(pObj)->nLeaves > (unsigned)(p->pPars->nLutSize - 1) )
        return 0;
    Vec_PtrForEachEntry( If_Obj_t *, p->vIfMappedSingles, pMate, i )
    {
        float Saving;
        if ( pMate == pObj || pMate->fIfLocked || pMate->pIfCandBest == NULL )
            continue;
        if ( !If_DualWindowFeasible( p, pObj, If_ObjCutBest(pObj), pObj->IfDepthLimit, pMate, If_ObjCutBest(pMate), pMate->IfDepthLimit, &WindowFlow, Leaves, &nLeaves ) )
            continue;
        /* Candidate existence is necessary but not sufficient after earlier
           greedy pairs change physical levels.  Check the two output levels
           separately because each output may depend on a different support set. */
        If_DualWindowLevels( p, vLevels, pObj, If_ObjCutBest(pObj), pMate, If_ObjCutBest(pMate), &Level0, &Level1 );
        if ( Level0 > pObj->IfDepthLimit || Level1 > pMate->IfDepthLimit )
            continue;
        Saving = If_ObjCutBest(pObj)->Area + If_ObjCutBest(pMate)->Area - WindowFlow;
        if ( Saving > BestSaving + p->fEpsilon )
        {
            int k, TrialDepth;
            /* Local window depth is not enough for serial/shared-fanout cases:
               accepting this pair may raise a leaf level seen by downstream LUTs.
               Try it transiently and keep it only if the whole cover remains
               within the sampled strict depth limit. */
            If_DualAddPair( p, pObj, pMate, Leaves, nLeaves );
            TrialDepth = If_DualComputeCoverDepth( p );
            If_DualPopLastPair( p, pObj, pMate );
            if ( TrialDepth > DepthLimit )
            {
                (*pnRejected)++;
                continue;
            }
            BestSaving = Saving;
            BestFlow = WindowFlow;
            pBestMate = pMate;
            nBestLeaves = nLeaves;
            BestLevel0 = Level0;
            BestLevel1 = Level1;
            for ( k = 0; k < nLeaves; k++ )
                BestLeaves[k] = Leaves[k];
        }
    }
    if ( pBestMate == NULL )
        return 0;
    If_ObjCutBest(pObj)->Area = BestFlow;
    If_DualAddPair( p, pObj, pBestMate, BestLeaves, nBestLeaves );
    Vec_IntWriteEntry( vLevels, pObj->Id, BestLevel0 );
    Vec_IntWriteEntry( vLevels, pBestMate->Id, BestLevel1 );
    return 1;
}

/* 遍历 mapped singles，执行一轮贪心 dual-output pairing。 */
static void If_DualMergePairs( If_Man_t * p, int DepthLimit ) 
{
    Vec_Int_t * vLevels;
    If_Obj_t * pObj;
    int i, nTried = 0, nAccepted = 0, nRejected = 0;
    if ( !p->pPars->fDualOutput ) 
        return;
    vLevels = Vec_IntStart( If_ManObjNum(p) );
    If_ManForEachObj( p, pObj, i )
        Vec_IntWriteEntry( vLevels, pObj->Id, If_DualObjLevel(p, vLevels, pObj) );
    Vec_PtrForEachEntry( If_Obj_t *, p->vIfMappedSingles, pObj, i )
    {
        if ( pObj->fIfLocked || If_ObjCutBest(pObj)->nLeaves > (unsigned)(p->pPars->nLutSize - 1) )
            continue;
        nTried++;
        nAccepted += If_DualTryMerge( p, vLevels, pObj, DepthLimit, &nRejected );
    }
    Abc_Print( 1, "      If-debug merge depth_limit=%d tried=%d accepted=%d rejected_depth=%d\n",
        DepthLimit, nTried, nAccepted, nRejected );
    Vec_IntFree( vLevels );
}

/* 在给定 depth limit 下构造 single cover、尝试 dual 合并并收集统计。 */
static int If_DualBuildCover( If_Man_t * p, int DepthLimit, If_DualStats_t * pStats )
{
    abctime clk, tReset, tSingles, tRebuild, tMerge, tStats;
    clk = Abc_Clock();
    memset( pStats, 0, sizeof(If_DualStats_t) );
    If_DualResetCoverState( p );
    tReset = Abc_Clock() - clk;
    clk = Abc_Clock();
    if ( !If_DualCoverSingles( p, DepthLimit ) )
    {
        tSingles = Abc_Clock() - clk;
        Abc_Print( 1, "      If-time-cover depth_limit=%d reset=%.2f sec singles=%.2f sec rebuild=0.00 sec merge=0.00 sec stats=0.00 sec\n",
            DepthLimit, If_DualTimeSec(tReset), If_DualTimeSec(tSingles) );
        return 0;
    }
    tSingles = Abc_Clock() - clk;
    clk = Abc_Clock();
    If_DualRebuildMappedSingles( p );
    tRebuild = Abc_Clock() - clk;
    clk = Abc_Clock();
    If_DualMergePairs( p, DepthLimit );
    tMerge = Abc_Clock() - clk;
    clk = Abc_Clock();
    If_DualCollectStats( p, pStats );
    tStats = Abc_Clock() - clk;
    Abc_Print( 1, "      If-time-cover depth_limit=%d reset=%.2f sec singles=%.2f sec rebuild=%.2f sec merge=%.2f sec stats=%.2f sec\n",
        DepthLimit, If_DualTimeSec(tReset), If_DualTimeSec(tSingles), If_DualTimeSec(tRebuild), If_DualTimeSec(tMerge), If_DualTimeSec(tStats) );
    return pStats->Depth <= DepthLimit;
}

/* 清空 best-cover 快照中深拷贝的 candidate/cut 数据。 */
static void If_DualSnapshotCutsClear( Vec_Ptr_t * vCands )
{
    If_Cand_t * pCand;
    int i;
    Vec_PtrForEachEntry( If_Cand_t *, vCands, pCand, i )
    {
        ABC_FREE( pCand );
        Vec_PtrWriteEntry( vCands, i, NULL );
    }
}

/* 保存当前 best cover：CutBest 深拷贝、depth limits、mapped roots 和 dual pairs。 */
static void If_DualSnapshotCover( If_Man_t * p, Vec_Ptr_t * vCands, Vec_Int_t * vLimits, Vec_Int_t * vMapped, Vec_Ptr_t ** pvPairs )
{
    If_Obj_t * pObj;
    int i;
    If_DualPairsFree( *pvPairs );
    *pvPairs = If_DualPairsDup( p->vIfDualPairs );
    If_DualSnapshotCutsClear( vCands );
    Vec_IntClear( vMapped );
    /* Deep-copy CutBest instead of storing candidate pointers.  Later depth
       iterations can overwrite a bucket's candidate with a lower-AF cut. */
    If_ManForEachObj( p, pObj, i )
    {
        If_Cand_t * pCand = NULL;
        if ( !If_ObjIsCi(pObj) && !If_ObjIsConst1(pObj) )
            pCand = If_DualCandAlloc( p, If_DualDepth( p, If_ObjCutBest(pObj)->Delay ), If_ObjCutBest(pObj), If_ObjCutBest(pObj)->Area );
        Vec_PtrWriteEntry( vCands, pObj->Id, pCand );
        Vec_IntWriteEntry( vLimits, pObj->Id, pObj->fIfMapped ? pObj->IfDepthLimit : IF_INFINITY );
    }
    Vec_PtrForEachEntry( If_Obj_t *, p->vIfMappedSingles, pObj, i )
        Vec_IntPush( vMapped, pObj->Id );
}

/* 从快照恢复 best cover，确保最终 ABC 抽取看到的是被选中的 CutBest。 */
static void If_DualRestoreCover( If_Man_t * p, Vec_Ptr_t * vCands, Vec_Int_t * vLimits, Vec_Int_t * vMapped, Vec_Ptr_t * vPairs )
{
    If_DualPair_t * pPair;
    If_Cand_t * pCand;
    If_Obj_t * pObj;
    int i, ObjId;
    If_DualResetCoverState( p );
    Vec_PtrClear( p->vIfMappedSingles );
    If_ManForEachObj( p, pObj, i )
    {
        pCand = (If_Cand_t *)Vec_PtrEntry( vCands, pObj->Id );
        if ( pCand == NULL )
            continue;
        If_CutCopy( p, If_ObjCutBest(pObj), &pCand->Cut );
        pObj->pIfCandBest = pCand;
        pObj->IfDepthLimit = Vec_IntEntry( vLimits, pObj->Id );
    }
    Vec_IntForEachEntry( vMapped, ObjId, i )
    {
        pObj = If_ManObj( p, ObjId );
        pObj->fIfMapped = 1;
        Vec_PtrPush( p->vIfMappedSingles, pObj );
    }
    Vec_PtrForEachEntry( If_DualPair_t *, vPairs, pPair, i )
    {
        If_Obj_t * pObj0 = If_ManObj( p, pPair->Obj0 );
        If_Obj_t * pObj1 = If_ManObj( p, pPair->Obj1 );
        If_DualAddPair( p, pObj0, pObj1, pPair->pLeaves, pPair->nLeaves );
    }
}

/* 比较两个 cover 的优劣：先看归一化 score，极小差异时用 LUT 数和实际 depth 打破平局。 */
static int If_DualStatsBetter( If_Man_t * p, If_DualStats_t * pStats, double BestScore, int BestDepth, int BestTotal, int BestLogicDepth )
{
    if ( pStats->Score < BestScore - p->fEpsilon )
        return 1;
    if ( pStats->Score > BestScore + p->fEpsilon )
        return 0;
    if ( BestDepth < 0 || pStats->nTotal < BestTotal )
        return 1;
    if ( pStats->nTotal > BestTotal )
        return 0; 
    return pStats->Depth < BestLogicDepth;
}

/* 评价一个 sampled depth limit，并在 score 更好时保存 best-cover 快照。 */
static int If_DualEvaluateDepthSample( If_Man_t * p, int DepthLimit, int AreaBase, int DepthTarget,
    double * pSampleScores, unsigned char * pSampled, int SampleOffset,
    Vec_Ptr_t * vBestCands, Vec_Int_t * vBestLimits, Vec_Int_t * vBestMapped, Vec_Ptr_t ** pvBestPairs,
    int * pBestDepth, double * pBestScore, int * pBestTotal, int * pBestLogicDepth )
{
    If_DualStats_t Stats;
    int iSample = DepthLimit - SampleOffset, iFlow;
    abctime clkFlow, clkCover, tFlow, tCover;
    if ( pSampled[iSample] )
        return 0;
    pSampled[iSample] = 1;
    p->nIfStrictMaxDepth = DepthLimit;
    p->fIfStrictCollect = 1;
    clkFlow = Abc_Clock();
    /* 每个 sampled depth 自己跑一次 FWD flow 迭代，只记录该 depth budget
       下可枚举到的候选；BWD coarse-to-fine 决定哪些 depth 会被 sample。 */
    for ( iFlow = 0; iFlow < Abc_MaxInt(1, p->pPars->nFlowIters); iFlow++ )
        If_ManPerformMappingRound( p, p->pPars->nCutsMax, 1, 0, 0, "StrictFlow" );
    tFlow = Abc_Clock() - clkFlow;
    p->fIfStrictCollect = 0;
    clkCover = Abc_Clock();
    if ( If_DualBuildCover( p, DepthLimit, &Stats ) )
    {
        tCover = Abc_Clock() - clkCover;
        If_DualUpdateScore( &Stats, AreaBase, DepthTarget );
        If_DualPrintStats( p, DepthLimit, "sample", &Stats );
        Abc_Print( 1, "      If-time-sample depth_limit=%d flow=%.2f sec cover=%.2f sec iter=%.2f sec\n",
            DepthLimit, If_DualTimeSec(tFlow), If_DualTimeSec(tCover), If_DualTimeSec(tFlow + tCover) );
        pSampleScores[iSample] = Stats.Score;
        if ( If_DualStatsBetter( p, &Stats, *pBestScore, *pBestDepth, *pBestTotal, *pBestLogicDepth ) )
        {
            *pBestDepth = DepthLimit;
            *pBestScore = Stats.Score;
            *pBestTotal = Stats.nTotal;
            *pBestLogicDepth = Stats.Depth;
            If_DualSnapshotCover( p, vBestCands, vBestLimits, vBestMapped, pvBestPairs );
        }
    }
    else
    {
        tCover = Abc_Clock() - clkCover;
        If_DualUpdateScore( &Stats, AreaBase, DepthTarget );
        if ( Stats.Depth > 0 || Stats.nTotal > 0 )
        {
            /* The BWD cover was built, but later pairing made the measured cover
               depth exceed this sampled limit, so the sample is rejected. */
            If_DualPrintStats( p, DepthLimit, "sample-overflow", &Stats );
            Abc_Print( 1, "    If-sample depth_limit=%d cover=depth_overflow max_depth=%d\n", DepthLimit, Stats.Depth );
        }
        else
        {
            /* No legal single-cover candidate was found for at least one queued
               node under this sampled depth limit. */
            If_DualPrintStats( p, DepthLimit, "sample-fail", &Stats );
            Abc_Print( 1, "    If-sample depth_limit=%d cover=failed\n", DepthLimit );
        }
        Abc_Print( 1, "      If-time-sample depth_limit=%d flow=%.2f sec cover=%.2f sec iter=%.2f sec\n",
            DepthLimit, If_DualTimeSec(tFlow), If_DualTimeSec(tCover), If_DualTimeSec(tFlow + tCover) );
        pSampleScores[iSample] = (double)ABC_INFINITY;
    }
    return 1;
}

/* 兼容入口：用 baseline depth 直接构造一次 strict/dual cover 并写回结果。 */
int If_DualFinalizeCover( If_Man_t * p )
{
    int DepthLimit = p->nIfStrictBaseDepth ? p->nIfStrictBaseDepth : If_DualDepth( p, p->RequiredGlo );
    If_DualStats_t Stats;
    If_DualResetCoverState( p );
    if ( !If_DualBuildCover( p, DepthLimit, &Stats ) )
    {
        Abc_Print( -1, "Strict/dual IF cover failed with depth limit %d.\n", DepthLimit );
        return 0;
    }
    If_ManComputeRequired( p );
    p->pPars->FinalDelay = p->RequiredGlo;
    p->pPars->FinalArea  = p->AreaGlo;
    If_DualUpdateScore( &Stats, Stats.nTotal, Stats.Depth );
    If_DualPrintStats( p, DepthLimit, "final", &Stats );
    return 1;
}

/* 把 classic IF baseline 的 CutBest 作为候选种子，保证搜索空间包含 baseline。 */
static void If_DualSeedBaselineCandidates( If_Man_t * p )
{
    If_Obj_t * pObj;
    int i;
    p->nIfStrictMaxDepth = p->nIfStrictBaseDepth;
    p->fIfStrictCollect = 1;
    If_ManForEachObj( p, pObj, i )
        if ( !If_ObjIsCi(pObj) && !If_ObjIsConst1(pObj) )
            If_DualRecordCandidate( p, pObj, If_ObjCutBest(pObj) );
    p->fIfStrictCollect = 0;
}

/* 计算 relaxed-depth 搜索上界：150% delay-optimal depth，至少放宽 10 层，且不小于 baseline。 */
static int If_DualSearchMaxDepth( If_Man_t * p )
{
    /* Explore up to 150% of the delay-optimal depth.  Baseline depth is kept
       as a lower bound in case classic IF is already deeper than min depth. */
    int MaxDepth = p->nIfStrictMinDepth + Abc_MaxInt(10, (p->nIfStrictMinDepth + 4) / 5);
    return Abc_MaxInt( MaxDepth, p->nIfStrictBaseDepth );
}

/* strict/dual 主流程：先跑 classic IF，再按多个 depth limit 收集候选并选 best cover。 */
int If_DualPerformStrictMapping( If_Man_t * p )
{
    If_DualStats_t Stats;
    Vec_Ptr_t * vBestCands, * vBestPairs = NULL;
    Vec_Int_t * vBestLimits, * vBestMapped, * vIntervals;
    double * pSampleScores = NULL;
    unsigned char * pSampled = NULL;
    int RetValue, d, i, k, MaxDepth, Range, Round;
    int BestDepth = -1, BestTotal = ABC_INFINITY, BestLogicDepth = ABC_INFINITY;
    int AreaBase = 1, DepthTarget = 1;
    double BestScore = (double)ABC_INFINITY;
    abctime clkTotal = Abc_Clock(), clkClassic, clkSeed;
    abctime tClassic, tSeed;
    clkClassic = Abc_Clock();
    RetValue = If_ManPerformMappingCombClassic( p );
    tClassic = Abc_Clock() - clkClassic;
    Abc_Print( 1, "  If-time classic=%.2f sec\n", If_DualTimeSec(tClassic) );
    if ( !RetValue )
        return 0;
    if ( p->nIfStrictMinDepth <= 0 )
        p->nIfStrictMinDepth = If_DualDepth( p, p->RequiredGlo );
    if ( p->nIfStrictBaseDepth < p->nIfStrictMinDepth )
        p->nIfStrictBaseDepth = p->nIfStrictMinDepth;
    MaxDepth = If_DualSearchMaxDepth( p );
    Abc_Print( 1, "  If-range min_depth=%d baseline_depth=%d max_depth_limit=%d n_limits=%d\n",
        p->nIfStrictMinDepth, p->nIfStrictBaseDepth, MaxDepth, MaxDepth - p->nIfStrictMinDepth + 1 );
    If_DualClearAll( p );
    /* The strict search is not allowed to lose the classic IF solution:
       seed its final CutBest choices before collecting stricter candidates. */
    If_DualSeedBaselineCandidates( p );
    vBestCands  = Vec_PtrStart( If_ManObjNum(p) );
    vBestLimits = Vec_IntStart( If_ManObjNum(p) );
    vBestMapped = Vec_IntAlloc( 1000 );
    Vec_IntFill( vBestLimits, If_ManObjNum(p), IF_INFINITY );
    clkSeed = Abc_Clock();
    if ( If_DualBuildCover( p, p->nIfStrictBaseDepth, &Stats ) )
    {
        DepthTarget = Abc_MaxInt( p->nIfStrictMinDepth, 1 );
        AreaBase = Abc_MaxInt( Stats.nTotal, 1 );
        If_DualUpdateScore( &Stats, AreaBase, DepthTarget );
        If_DualPrintStats( p, p->nIfStrictBaseDepth, "seed", &Stats );
        BestDepth = p->nIfStrictBaseDepth;
        BestScore = Stats.Score;
        BestTotal = Stats.nTotal;
        BestLogicDepth = Stats.Depth;
        If_DualSnapshotCover( p, vBestCands, vBestLimits, vBestMapped, &vBestPairs );
    }
    tSeed = Abc_Clock() - clkSeed;
    Abc_Print( 1, "  If-time seed_cover=%.2f sec\n", If_DualTimeSec(tSeed) );

    Range = MaxDepth - p->nIfStrictMinDepth + 1;
    pSampleScores = ABC_ALLOC( double, Range );
    pSampled = ABC_CALLOC( unsigned char, Range );
    for ( i = 0; i < Range; i++ )
        pSampleScores[i] = (double)ABC_INFINITY;
    vIntervals = Vec_IntAlloc( 16 );
    Vec_IntPushTwo( vIntervals, p->nIfStrictMinDepth, MaxDepth );
    Abc_Print( 1, "  If-sample adaptive=quartile keep_segments=2 mu=%.2f area_base=%d depth_target=%d\n",
        If_DualScoreMu(), AreaBase, DepthTarget );
    for ( Round = 0; Vec_IntSize(vIntervals) > 0 && Round < 16; Round++ )
    {
        Vec_Int_t * vSegments = Vec_IntAlloc( 16 );
        int nEvalRound = 0, nSegs, BestLo0 = -1, BestHi0 = -1, BestLo1 = -1, BestHi1 = -1;
        double BestSeg0 = (double)ABC_INFINITY, BestSeg1 = (double)ABC_INFINITY;
        for ( i = 0; i < Vec_IntSize(vIntervals); i += 2 )
        {
            int Lo = Vec_IntEntry( vIntervals, i );
            int Hi = Vec_IntEntry( vIntervals, i + 1 );
            int Width = Hi - Lo;
            if ( Width <= 3 )
            {
                for ( d = Lo; d <= Hi; d++ )
                    nEvalRound += If_DualEvaluateDepthSample( p, d, AreaBase, DepthTarget,
                        pSampleScores, pSampled, p->nIfStrictMinDepth,
                        vBestCands, vBestLimits, vBestMapped, &vBestPairs,
                        &BestDepth, &BestScore, &BestTotal, &BestLogicDepth );
                continue;
            }
            {
                int Points[5], nPoints = 0, Prev = -1;
                Points[0] = Lo;
                Points[1] = Lo + (Width + 3) / 4;
                Points[2] = Lo + (Width + 1) / 2;
                Points[3] = Lo + (3 * Width + 3) / 4;
                Points[4] = Hi;
                for ( k = 0; k < 5; k++ )
                {
                    d = Abc_MinInt( Hi, Abc_MaxInt( Lo, Points[k] ) );
                    if ( d == Prev )
                        continue;
                    Points[nPoints++] = d;
                    Prev = d;
                    nEvalRound += If_DualEvaluateDepthSample( p, d, AreaBase, DepthTarget,
                        pSampleScores, pSampled, p->nIfStrictMinDepth,
                        vBestCands, vBestLimits, vBestMapped, &vBestPairs,
                        &BestDepth, &BestScore, &BestTotal, &BestLogicDepth );
                }
                for ( k = 0; k + 1 < nPoints; k++ )
                    if ( Points[k+1] > Points[k] )
                        Vec_IntPushTwo( vSegments, Points[k], Points[k+1] );
            }
        }
        nSegs = Vec_IntSize(vSegments) / 2;
        for ( i = 0; i < Vec_IntSize(vSegments); i += 2 )
        {
            int Lo = Vec_IntEntry( vSegments, i );
            int Hi = Vec_IntEntry( vSegments, i + 1 );
            double S0 = pSampleScores[Lo - p->nIfStrictMinDepth];
            double S1 = pSampleScores[Hi - p->nIfStrictMinDepth];
            double S = S0 < S1 ? S0 : S1;
            if ( S < BestSeg0 )
            {
                BestSeg1 = BestSeg0; BestLo1 = BestLo0; BestHi1 = BestHi0;
                BestSeg0 = S;        BestLo0 = Lo;      BestHi0 = Hi;
            }
            else if ( S < BestSeg1 )
            {
                BestSeg1 = S;        BestLo1 = Lo;      BestHi1 = Hi;
            }
        }
        Abc_Print( 1, "  If-sample-round round=%d intervals=%d evals=%d candidate_segments=%d best_segment=[%d,%d] second_segment=[%d,%d]\n",
            Round, Vec_IntSize(vIntervals) / 2, nEvalRound, nSegs, BestLo0, BestHi0, BestLo1, BestHi1 );
        Vec_IntClear( vIntervals );
        if ( BestLo0 >= 0 && BestHi0 - BestLo0 > 1 )
            Vec_IntPushTwo( vIntervals, BestLo0, BestHi0 );
        if ( BestLo1 >= 0 && BestHi1 - BestLo1 > 1 && (BestLo1 != BestLo0 || BestHi1 != BestHi0) )
            Vec_IntPushTwo( vIntervals, BestLo1, BestHi1 );
        Vec_IntFree( vSegments );
    }
    Vec_IntFree( vIntervals );
    if ( BestDepth < 0 )
    {
        Abc_Print( -1, "Strict/dual IF cover failed for all depth limits [%d, %d].\n", p->nIfStrictMinDepth, MaxDepth );
        If_DualSnapshotCutsClear( vBestCands );
        Vec_PtrFree( vBestCands );
        Vec_IntFree( vBestLimits );
        Vec_IntFree( vBestMapped );
        If_DualPairsFree( vBestPairs );
        ABC_FREE( pSampleScores );
        ABC_FREE( pSampled );
        return 0;
    }
    If_DualRestoreCover( p, vBestCands, vBestLimits, vBestMapped, vBestPairs );
    If_DualCollectStats( p, &Stats );
    If_DualUpdateScore( &Stats, AreaBase, DepthTarget );
    If_DualPrintStats( p, BestDepth, "best", &Stats );
    If_DualSnapshotCutsClear( vBestCands );
    Vec_PtrFree( vBestCands );
    Vec_IntFree( vBestLimits );
    Vec_IntFree( vBestMapped );
    If_DualPairsFree( vBestPairs );
    ABC_FREE( pSampleScores );
    ABC_FREE( pSampled );
    If_ManComputeRequired( p );
    p->pPars->FinalDelay = p->RequiredGlo;
    p->pPars->FinalArea  = p->AreaGlo;
    Abc_Print( 1, "  If-time total=%.2f sec\n", If_DualTimeSec(Abc_Clock() - clkTotal) );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                     ABC NETWORK ATTRIBUTES                        ///
////////////////////////////////////////////////////////////////////////

/* ABC 属性析构函数：释放挂在 mapped network 节点上的 dual 属性。 */
static void If_DualAttrFree( void * pMan, void * pObj )
{
    (void)pMan;
    ABC_FREE( pObj );
}

/* 将 IF dual pair 转成 ABC network 属性，供 write_verilog -K 输出 dual_lutN。 */
void If_DualTransferAttrs( If_Man_t * pIfMan, void * pNtkNewVoid )
{
    Abc_Ntk_t * pNtkNew = (Abc_Ntk_t *)pNtkNewVoid;
    Vec_Att_t * pAttrs;
    If_DualPair_t * pPair;
    int i;
    if ( !pIfMan->pPars->fDualOutput || pIfMan->vIfDualPairs == NULL || Vec_PtrSize(pIfMan->vIfDualPairs) == 0 )
        return;
    pAttrs = Vec_AttAlloc( Abc_NtkObjNumMax(pNtkNew) + 1, NULL, NULL, NULL, If_DualAttrFree );
    Vec_PtrWriteEntry( pNtkNew->vAttrs, VEC_ATTR_DATA1, pAttrs );
    Vec_PtrForEachEntry( If_DualPair_t *, pIfMan->vIfDualPairs, pPair, i )
    {
        If_Obj_t * pIfObj0 = If_ManObj( pIfMan, pPair->Obj0 );
        If_Obj_t * pIfObj1 = If_ManObj( pIfMan, pPair->Obj1 );
        Abc_Obj_t * pObj0 = (Abc_Obj_t *)If_ObjCopy( pIfObj0 );
        Abc_Obj_t * pObj1 = (Abc_Obj_t *)If_ObjCopy( pIfObj1 );
        If_DualAttr_t * pAttr0, * pAttr1;
        int k;
        if ( pObj0 == NULL || pObj1 == NULL )
            continue;
        pAttr0 = ABC_CALLOC( If_DualAttr_t, 1 );
        pAttr1 = ABC_CALLOC( If_DualAttr_t, 1 );
        pAttr0->iMate = pObj1->Id;
        pAttr0->nLutSize = pIfMan->pPars->nLutSize;
        pAttr1->iMate = pObj0->Id;
        pAttr1->nLutSize = pIfMan->pPars->nLutSize;
        pAttr0->nLeaves = pAttr1->nLeaves = pPair->nLeaves;
        for ( k = 0; k < pPair->nLeaves; k++ )
        {
            If_Obj_t * pIfLeaf = If_ManObj( pIfMan, pPair->pLeaves[k] );
            Abc_Obj_t * pLeaf = (Abc_Obj_t *)If_ObjCopy( pIfLeaf );
            if ( pLeaf == NULL )
                break;
            pAttr0->pLeaves[k] = pAttr1->pLeaves[k] = pLeaf->Id;
        }
        if ( k != pPair->nLeaves )
        {
            ABC_FREE( pAttr0 );
            ABC_FREE( pAttr1 );
            continue;
        }
        Vec_AttWriteEntry( pAttrs, pObj0->Id, pAttr0 );
        Vec_AttWriteEntry( pAttrs, pObj1->Id, pAttr1 );
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
