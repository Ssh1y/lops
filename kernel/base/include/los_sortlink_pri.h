#ifndef _LOS_SORTLINK_PRI_H
#define _LOS_SORTLINK_PRI_H

#include "los_typedef.h"
#include "los_list.h"

#ifdef __cplusplus
#if __cplusplus
extern "C" {
#endif /* __cplusplus */
#endif /* __cplusplus */

typedef struct {
    LOS_DL_LIST sortLinkNode;
    UINT64      responseTime;
#ifdef LOSCFG_KERNEL_SMP
    UINT32      cpuid;
#endif
} SortLinkList;

typedef struct {
    LOS_DL_LIST sortLink;
    UINT32      nodeNum;
    // SPIN_LOCK_S spinLock;     /* swtmr sort link spin lock */
} SortLinkAttribute;

#define OS_SORT_LINK_INVALID_TIME ((UINT64)-1)
#define SET_SORTLIST_VALUE(sortList, value) (((SortLinkList *)(sortList))->responseTime = (value))
#define GET_SORTLIST_VALUE(sortList) (((SortLinkList *)(sortList))->responseTime)

STATIC INLINE VOID OsDeleteNodeSortLink(SortLinkAttribute *sortLinkHeader, SortLinkList *sortList)
{
    LOS_ListDelete(&sortList->sortLinkNode);
    SET_SORTLIST_VALUE(sortList, OS_SORT_LINK_INVALID_TIME);
    sortLinkHeader->nodeNum--;
}

STATIC INLINE UINT64 OsGetSortLinkNextExpireTime(SortLinkAttribute *sortHeader, UINT64 startTime, UINT32 tickPrecision)
{
    LOS_DL_LIST *head = &sortHeader->sortLink;
    LOS_DL_LIST *list = head->pstNext;

    // LOS_SpinLock(&sortHeader->spinLock);
    if (LOS_ListEmpty(head)) {
        // LOS_SpinUnlock(&sortHeader->spinLock);
        return OS_SORT_LINK_INVALID_TIME - tickPrecision;
    }

    SortLinkList *listSorted = LOS_DL_LIST_ENTRY(list, SortLinkList, sortLinkNode);
    if (listSorted->responseTime <= (startTime + tickPrecision)) {
        // LOS_SpinUnlock(&sortHeader->spinLock);
        return startTime + tickPrecision;
    }

    // LOS_SpinUnlock(&sortHeader->spinLock);
    return listSorted->responseTime;
}

STATIC INLINE UINT32 OsGetSortLinkNodeNum(const SortLinkAttribute *head)
{
    return head->nodeNum;
}

STATIC INLINE UINT16 OsGetSortLinkNodeCpuid(const SortLinkList *node)
{
#ifdef LOSCFG_KERNEL_SMP
    return node->cpuid;
#else
    return 0;
#endif
}

VOID OsSortLinkInit(SortLinkAttribute *sortLinkHeader);
VOID OsAdd2SortLink(SortLinkAttribute *head, SortLinkList *node, UINT64 responseTime, UINT16 idleCpu);
VOID OsDeleteFromSortLink(SortLinkAttribute *head, SortLinkList *node);
UINT64 OsSortLinkGetTargetExpireTime(UINT64 currTime, const SortLinkList *targetSortList);
UINT64 OsSortLinkGetNextExpireTime(UINT64 currTime, const SortLinkAttribute *sortLinkHeader);
UINT32 OsSortLinkAdjustNodeResponseTime(SortLinkAttribute *head, SortLinkList *node, UINT64 responseTime);

#ifdef __cplusplus
#if __cplusplus
}
#endif /* __cplusplus */
#endif /* __cplusplus */

#endif /* _LOS_SORTLINK_PRI_H */
