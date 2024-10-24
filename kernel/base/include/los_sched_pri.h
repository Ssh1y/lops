/*
 * Copyright (c) 2013-2019 Huawei Technologies Co., Ltd. All rights reserved.
 * Copyright (c) 2020-2023 Huawei Device Co., Ltd. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice, this list of
 *    conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list
 *    of conditions and the following disclaimer in the documentation and/or other materials
 *    provided with the distribution.
 *
 * 3. Neither the name of the copyright holder nor the names of its contributors may be used
 *    to endorse or promote products derived from this software without specific prior written
 *    permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#ifndef _LOS_SCHED_PRI_H
#define _LOS_SCHED_PRI_H

#include "los_sortlink_pri.h"
#include "los_sys_pri.h"
#include "los_task.h"

/* for compile */
#include "los_hw_cpu.h"
#include <stdlib.h>
#include <string.h>

#ifdef __cplusplus
#if __cplusplus
extern "C" {
#endif /* __cplusplus */
#endif /* __cplusplus */

#define OS_SCHED_MINI_PERIOD          (OS_SYS_CLOCK / LOSCFG_BASE_CORE_TICK_PER_SECOND_MINI)
#define OS_TICK_RESPONSE_PRECISION    (UINT32)((OS_SCHED_MINI_PERIOD * 75) / 100)
#define OS_SCHED_MAX_RESPONSE_TIME    OS_SORT_LINK_INVALID_TIME
#define OS_SCHED_TICK_TO_CYCLE(ticks) ((UINT64)ticks * OS_CYCLE_PER_TICK)
#define AFFI_MASK_TO_CPUID(mask)      ((UINT16)((mask) - 1))

#define OS_SCHED_EDF_MIN_RUNTIME    100 /* 100 us */
#define OS_SCHED_EDF_MIN_DEADLINE   400 /* 400 us */
#define OS_SCHED_EDF_MAX_DEADLINE   5000000 /* 5 s */

extern UINT32 g_taskScheduled;
#define OS_SCHEDULER_ACTIVE (g_taskScheduled & (1U << ArchCurrCpuid()))
#define OS_SCHEDULER_ALL_ACTIVE (g_taskScheduled == LOSCFG_KERNEL_CPU_MASK)

typedef struct TagTaskCB LosTaskCB;
typedef BOOL (*SCHED_TL_FIND_FUNC)(UINTPTR, UINTPTR);

STATIC INLINE UINT64 OsGetCurrSchedTimeCycle(VOID)
{
    // return HalClockGetCycles();
    return 100; //todo 修改逻辑
}

typedef enum {
    INT_NO_RESCH = 0x0,   /* no needs to schedule */
    INT_PEND_RESCH = 0x1, /* pending schedule flag */
    INT_PEND_TICK = 0x2,  /* pending tick */
} SchedFlag;

// #define OS_PRIORITY_QUEUE_NUM 32
#define OS_PRIORITY_QUEUE_NUM 12
typedef struct {
    LOS_DL_LIST priQueList[OS_PRIORITY_QUEUE_NUM];
    UINT32      readyTasks[OS_PRIORITY_QUEUE_NUM];
    UINT32      queueBitmap;
} HPFQueue;

typedef struct {
    HPFQueue queueList[OS_PRIORITY_QUEUE_NUM];
    UINT32   queueBitmap;
} HPFRunqueue;

typedef struct {
    LOS_DL_LIST root;
    LOS_DL_LIST waitList;
    UINT64 period;
} EDFRunqueue;

typedef struct {
    SortLinkAttribute timeoutQueue; /* 任务超时队列 */
    HPFRunqueue       *hpfRunqueue;
    EDFRunqueue       *edfRunqueue;
    UINT64            responseTime; /* 当前CPU滴答中断的响应时间 */
    UINT32            responseID;   /* 当前CPU滴答中断的响应ID */
    LosTaskCB         *idleTask;   /* 空闲任务ID */
    UINT32            taskLockCnt;  /* 任务锁标志 */
    UINT32            schedFlag;    /* 挂起调度器标志 */
} SchedRunqueue;

extern SchedRunqueue g_schedRunqueue[LOSCFG_KERNEL_CORE_NUM];

VOID OsSchedExpireTimeUpdate(VOID);

STATIC INLINE SchedRunqueue *OsSchedRunqueue(VOID)
{
    return &g_schedRunqueue[ArchCurrCpuid()];
}

STATIC INLINE SchedRunqueue *OsSchedRunqueueByID(UINT16 id)
{
    return &g_schedRunqueue[id];
}

STATIC INLINE UINT32 OsSchedLockCountGet(VOID)
{
    return OsSchedRunqueue()->taskLockCnt;
}

STATIC INLINE VOID OsSchedLockSet(UINT32 count)
{
    OsSchedRunqueue()->taskLockCnt = count;
}

STATIC INLINE VOID OsSchedLock(VOID)
{
    OsSchedRunqueue()->taskLockCnt++;
}

STATIC INLINE VOID OsSchedUnlock(VOID)
{
    OsSchedRunqueue()->taskLockCnt--;
}

STATIC INLINE BOOL OsSchedUnlockResch(VOID)
{
    SchedRunqueue *rq = OsSchedRunqueue();
    if (rq->taskLockCnt > 0) {
        rq->taskLockCnt--;
        if ((rq->taskLockCnt == 0) && (rq->schedFlag & INT_PEND_RESCH) && OS_SCHEDULER_ACTIVE) {
            return TRUE;
        }
    }

    return FALSE;
}

STATIC INLINE BOOL OsSchedIsLock(VOID)
{
    return (OsSchedRunqueue()->taskLockCnt != 0);
}

/* Check if preemptible with counter flag */
STATIC INLINE BOOL OsPreemptable(VOID)
{
    SchedRunqueue *rq = OsSchedRunqueue();
    /*
     * Unlike OsPreemptableInSched, the int may be not disabled when OsPreemptable
     * is called, needs manually disable interrupt, to prevent current task from
     * being migrated to another core, and get the wrong preemptable status.
     */
    // UINT32 intSave = LOS_IntLock();
    BOOL preemptible = (rq->taskLockCnt == 0);
    if (!preemptible) {
        /* Set schedule flag if preemption is disabled */
        rq->schedFlag |= INT_PEND_RESCH;
    }
    // LOS_IntRestore(intSave);
    return preemptible;
}

STATIC INLINE BOOL OsPreemptableInSched(VOID)
{
    BOOL preemptible = FALSE;
    SchedRunqueue *rq = OsSchedRunqueue();

#ifdef LOSCFG_KERNEL_SMP
    /*
     * For smp systems, schedule must hold the task spinlock, and this counter
     * will increase by 1 in that case.
     */
    preemptible = (rq->taskLockCnt == 1);

#else
    preemptible = (rq->taskLockCnt == 0);
#endif
    if (!preemptible) {
        /* Set schedule flag if preemption is disabled */
        rq->schedFlag |= INT_PEND_RESCH;
    }

    return preemptible;
}

STATIC INLINE LosTaskCB *OsSchedRunqueueIdleGet(VOID)
{
    return OsSchedRunqueue()->idleTask;
}

STATIC INLINE VOID OsSchedRunqueuePendingSet(VOID)
{
    OsSchedRunqueue()->schedFlag |= INT_PEND_RESCH;
}

#define LOS_SCHED_NORMAL    0U
#define LOS_SCHED_FIFO      1U
#define LOS_SCHED_RR        2U
#define LOS_SCHED_IDLE      3U
#define LOS_SCHED_DEADLINE  6U

typedef struct {
    UINT16 policy;
    /* HPF scheduling parameters */
    UINT16 basePrio;
    UINT16 priority;
    UINT32 timeSlice;

    /* EDF scheduling parameters */
    INT32  runTimeUs;
    UINT32 deadlineUs;
    UINT32 periodUs;
} SchedParam;

typedef struct {
    UINT16  policy; /* 该字段必须存在于所有调度策略中，并且必须是结构中的第一个字段 */
    UINT16  basePrio;
    UINT16  priority;
    UINT32  initTimeSlice; /* 周期 */
    UINT32  priBitmap; /* 用于记录任务优先级变化的位图，优先级不能大于31 */
} SchedHPF;

#define EDF_UNUSED       0
#define EDF_NEXT_PERIOD  1
#define EDF_WAIT_FOREVER 2
#define EDF_INIT         3
typedef struct {
    UINT16 policy;
    UINT16 cpuid;
    UINT32 flags;
    INT32  runTime;    /* 周期 */
    UINT64 deadline;   /* 截止时间 >> 运行时间 */
    UINT64 period;     /* 周期 >= 截止时间 */
    UINT64 finishTime; /* 开始时间 + 截止时间 */
} SchedEDF;

typedef struct {
    union {
        SchedEDF edf;
        SchedHPF hpf;
    };
} SchedPolicy;

typedef struct {
    VOID (*dequeue)(SchedRunqueue *rq, LosTaskCB *taskCB);
    VOID (*enqueue)(SchedRunqueue *rq, LosTaskCB *taskCB);
    VOID (*start)(SchedRunqueue *rq, LosTaskCB *taskCB);
    // VOID (*exit)(LosTaskCB *taskCB);
    UINT64 (*waitTimeGet)(LosTaskCB *taskCB);
    // UINT32 (*wait)(LosTaskCB *runTask, LOS_DL_LIST *list, UINT32 timeout);
    // VOID (*wake)(LosTaskCB *taskCB);
    // BOOL (*schedParamModify)(LosTaskCB *taskCB, const SchedParam *param);
    // UINT32 (*schedParamGet)(const LosTaskCB *taskCB, SchedParam *param);
    // UINT32 (*delay)(LosTaskCB *taskCB, UINT64 waitTime);
    // VOID (*yield)(LosTaskCB *taskCB);
    // UINT32 (*suspend)(LosTaskCB *taskCB);
    // UINT32 (*resume)(LosTaskCB *taskCB, BOOL *needSched);
    UINT64 (*deadlineGet)(const LosTaskCB *taskCB);
    VOID (*timeSliceUpdate)(SchedRunqueue *rq, LosTaskCB *taskCB, UINT64 currTime);
    // INT32 (*schedParamCompare)(const SchedPolicy *sp1, const SchedPolicy *sp2);
    // VOID (*priorityInheritance)(LosTaskCB *owner, const SchedParam *param);
    // VOID (*priorityRestore)(LosTaskCB *owner, const LOS_DL_LIST *list, const SchedParam *param);
} SchedOps;

/**
 * @ingroup los_sched
 * Define a usable task priority.
 *
 * Highest task priority.
 */
#define OS_TASK_PRIORITY_HIGHEST    0

/**
 * @ingroup los_sched
 * Define a usable task priority.
 *
 * Lowest task priority.
 */
// #define OS_TASK_PRIORITY_LOWEST     31
#define OS_TASK_PRIORITY_LOWEST     11

/**
 * @ingroup los_sched
 * Flag that indicates the task or task control block status.
 *
 * The task is init.
 */
#define OS_TASK_STATUS_INIT         0x0001U

/**
 * @ingroup los_sched
 * Flag that indicates the task or task control block status.
 *
 * The task is ready.
 */
#define OS_TASK_STATUS_READY        0x0002U

/**
 * @ingroup los_sched
 * Flag that indicates the task or task control block status.
 *
 * The task is running.
 */
#define OS_TASK_STATUS_RUNNING      0x0004U

/**
 * @ingroup los_sched
 * Flag that indicates the task or task control block status.
 *
 * The task is suspended.
 */
#define OS_TASK_STATUS_SUSPENDED    0x0008U

/**
 * @ingroup los_sched
 * Flag that indicates the task or task control block status.
 *
 * The task is blocked.
 */
#define OS_TASK_STATUS_PENDING      0x0010U

/**
 * @ingroup los_sched
 * Flag that indicates the task or task control block status.
 *
 * The task is delayed.
 */
#define OS_TASK_STATUS_DELAY        0x0020U

/**
 * @ingroup los_sched
 * Flag that indicates the task or task control block status.
 *
 * The time for waiting for an event to occur expires.
 */
#define OS_TASK_STATUS_TIMEOUT      0x0040U

/**
 * @ingroup los_sched
 * Flag that indicates the task or task control block status.
 *
 * The task is pend for a period of time.
 */
#define OS_TASK_STATUS_PEND_TIME    0x0080U

/**
 * @ingroup los_sched
 * Flag that indicates the task or task control block status.
 *
 * The task is exit.
 */
#define OS_TASK_STATUS_EXIT         0x0100U

#define OS_TASK_STATUS_BLOCKED     (OS_TASK_STATUS_INIT | OS_TASK_STATUS_PENDING | \
                                    OS_TASK_STATUS_DELAY | OS_TASK_STATUS_PEND_TIME)

/**
 * @ingroup los_task
 * Flag that indicates the task or task control block status.
 *
 * The delayed operation of this task is frozen.
 */
#define OS_TASK_STATUS_FROZEN       0x0200U

#define OS_TCB_NAME_LEN             32

typedef struct TagTaskCB {
    UINT16          taskStatus;         /* 任务状态 */

    UINT64          startTime;          /* 每个任务阶段的开始时间 */
    UINT64          waitTime;           /* 任务延迟时间，滴答数 */
    UINT64          irqStartTime;       /* 中断开始时间 */
    UINT32          irqUsedTime;        /* 中断消耗时间 */
    INT32           timeSlice;          /* 任务剩余时间片 */
    SortLinkList    sortList;           /* 任务排序链节点 */
    const SchedOps  *ops;
    SchedPolicy     sp;

    UINT32          taskID;             /* 任务ID */
    LOS_DL_LIST     pendList;           /* 任务挂起节点 */
    UINTPTR         processCB;          /* 所属进程 */
} LosTaskCB;

extern LosTaskCB *g_runTask; // 声明一个全局运行任务

STATIC INLINE BOOL OsTaskIsRunning(const LosTaskCB *taskCB)
{
    return ((taskCB->taskStatus & OS_TASK_STATUS_RUNNING) != 0);
}

STATIC INLINE BOOL OsTaskIsReady(const LosTaskCB *taskCB)
{
    return ((taskCB->taskStatus & OS_TASK_STATUS_READY) != 0);
}

STATIC INLINE BOOL OsTaskIsInactive(const LosTaskCB *taskCB)
{
    return ((taskCB->taskStatus & (OS_TASK_STATUS_INIT | OS_TASK_STATUS_EXIT)) != 0);
}

STATIC INLINE BOOL OsTaskIsPending(const LosTaskCB *taskCB)
{
    return ((taskCB->taskStatus & OS_TASK_STATUS_PENDING) != 0);
}

STATIC INLINE BOOL OsTaskIsSuspended(const LosTaskCB *taskCB)
{
    return ((taskCB->taskStatus & OS_TASK_STATUS_SUSPENDED) != 0);
}

STATIC INLINE BOOL OsTaskIsBlocked(const LosTaskCB *taskCB)
{
    return ((taskCB->taskStatus & (OS_TASK_STATUS_SUSPENDED | OS_TASK_STATUS_PENDING | OS_TASK_STATUS_DELAY)) != 0);
}

STATIC INLINE BOOL OsSchedPolicyIsEDF(const LosTaskCB *taskCB)
{
    const SchedEDF *sched = (const SchedEDF *)&taskCB->sp;
    return (sched->policy == LOS_SCHED_DEADLINE);
}

STATIC INLINE LosTaskCB *OsCurrTaskGet(VOID)
{
    // return (LosTaskCB *)ArchCurrTaskGet();
    return g_runTask;
}

STATIC INLINE VOID OsCurrTaskSet(LosTaskCB *task)
{
    // ArchCurrTaskSet(task);
    g_runTask = task;
}

STATIC INLINE VOID OsSchedIrqUsedTimeUpdate(VOID)
{
    LosTaskCB *runTask = OsCurrTaskGet();
    runTask->irqUsedTime = OsGetCurrSchedTimeCycle() - runTask->irqStartTime;
}

STATIC INLINE VOID OsSchedIrqStartTime(VOID)
{
    LosTaskCB *runTask = OsCurrTaskGet();
    runTask->irqStartTime = OsGetCurrSchedTimeCycle();
}

#ifdef LOSCFG_KERNEL_SMP
STATIC INLINE VOID IdleRunqueueFind(UINT16 *idleCpuid)
{
    SchedRunqueue *idleRq = OsSchedRunqueueByID(0);
    UINT32 nodeNum = OsGetSortLinkNodeNum(&idleRq->timeoutQueue);
    UINT16 cpuid = 1;
    do {
        SchedRunqueue *rq = OsSchedRunqueueByID(cpuid);
        UINT32 temp = OsGetSortLinkNodeNum(&rq->timeoutQueue);
        if (nodeNum > temp) {
            *idleCpuid = cpuid;
            nodeNum = temp;
        }
        cpuid++;
    } while (cpuid < LOSCFG_KERNEL_CORE_NUM);
}
#endif

STATIC INLINE VOID OsSchedTimeoutQueueAdd(LosTaskCB *taskCB, UINT64 responseTime)
{
#ifdef LOSCFG_KERNEL_SMP
    UINT16 cpuid = AFFI_MASK_TO_CPUID(taskCB->cpuAffiMask);
    if (cpuid >= LOSCFG_KERNEL_CORE_NUM) {
        cpuid = 0;
        IdleRunqueueFind(&cpuid);
    }
#else
    UINT16 cpuid = 0;
#endif

    SchedRunqueue *rq = OsSchedRunqueueByID(cpuid);
    OsAdd2SortLink(&rq->timeoutQueue, &taskCB->sortList, responseTime, cpuid);
#ifdef LOSCFG_KERNEL_SMP
    if ((cpuid != ArchCurrCpuid()) && (responseTime < rq->responseTime)) {
        rq->schedFlag |= INT_PEND_TICK;
        LOS_MpSchedule(CPUID_TO_AFFI_MASK(cpuid));
    }
#endif
}

STATIC INLINE VOID OsSchedTimeoutQueueDelete(LosTaskCB *taskCB)
{
    SortLinkList *node = &taskCB->sortList;
#ifdef LOSCFG_KERNEL_SMP
    SchedRunqueue *rq = OsSchedRunqueueByID(node->cpuid);
#else
    SchedRunqueue *rq = OsSchedRunqueueByID(0);
#endif
    UINT64 oldResponseTime = GET_SORTLIST_VALUE(node);
    OsDeleteFromSortLink(&rq->timeoutQueue, node);
    if (oldResponseTime <= rq->responseTime) {
        rq->responseTime = OS_SCHED_MAX_RESPONSE_TIME;
    }
}

STATIC INLINE UINT32 OsSchedTimeoutQueueAdjust(LosTaskCB *taskCB, UINT64 responseTime)
{
    UINT32 ret;
    SortLinkList *node = &taskCB->sortList;
#ifdef LOSCFG_KERNEL_SMP
    UINT16 cpuid = node->cpuid;
#else
    UINT16 cpuid = 0;
#endif
    SchedRunqueue *rq = OsSchedRunqueueByID(cpuid);
    ret = OsSortLinkAdjustNodeResponseTime(&rq->timeoutQueue, node, responseTime);
    if (ret == LOS_OK) {
        rq->schedFlag |= INT_PEND_TICK;
    }
    return ret;
}

STATIC INLINE VOID SchedTaskFreeze(LosTaskCB *taskCB)
{
    UINT64 responseTime;

#ifdef LOSCFG_KERNEL_PM
    if (!OsIsPmMode()) {
        return;
    }
#endif

    if (!(taskCB->taskStatus & (OS_TASK_STATUS_PEND_TIME | OS_TASK_STATUS_DELAY))) {
        return;
    }

    responseTime = GET_SORTLIST_VALUE(&taskCB->sortList);
    OsSchedTimeoutQueueDelete(taskCB);
    SET_SORTLIST_VALUE(&taskCB->sortList, responseTime);
    taskCB->taskStatus |= OS_TASK_STATUS_FROZEN;
    return;
}

STATIC INLINE VOID SchedTaskUnfreeze(LosTaskCB *taskCB)
{
    UINT64 currTime, responseTime;

    if (!(taskCB->taskStatus & OS_TASK_STATUS_FROZEN)) {
        return;
    }

    taskCB->taskStatus &= ~OS_TASK_STATUS_FROZEN;
    currTime = OsGetCurrSchedTimeCycle();
    responseTime = GET_SORTLIST_VALUE(&taskCB->sortList);
    if (responseTime > currTime) {
        OsSchedTimeoutQueueAdd(taskCB, responseTime);
        return;
    }

    SET_SORTLIST_VALUE(&taskCB->sortList, OS_SORT_LINK_INVALID_TIME);
    if (taskCB->taskStatus & OS_TASK_STATUS_PENDING) {
        LOS_ListDelete(&taskCB->pendList);
    }
    taskCB->taskStatus &= ~OS_TASK_STATUS_BLOCKED;
    return;
}

/*
 * Schedule flag, one bit represents one core.
 * This flag is used to prevent kernel scheduling before OSStartToRun.
 */
#define OS_SCHEDULER_SET(cpuid) do {     \
    g_taskScheduled |= (1U << (cpuid));  \
} while (0);

#define OS_SCHEDULER_CLR(cpuid) do {     \
    g_taskScheduled &= ~(1U << (cpuid)); \
} while (0);

#ifdef LOSCFG_KERNEL_SCHED_PLIMIT
BOOL OsSchedLimitCheckTime(LosTaskCB *task);
#endif

STATIC INLINE LosTaskCB *EDFRunqueueTopTaskGet(EDFRunqueue *rq)
{
    LOS_DL_LIST *root = &rq->root;
    if (LOS_ListEmpty(root)) {
        return NULL;
    }

    return LOS_DL_LIST_ENTRY(LOS_DL_LIST_FIRST(root), LosTaskCB, pendList);
}

STATIC INLINE LosTaskCB *HPFRunqueueTopTaskGet(HPFRunqueue *rq)
{
    LosTaskCB *newTask = NULL;
    UINT32 baseBitmap = rq->queueBitmap;
#ifdef LOSCFG_KERNEL_SMP
    UINT32 cpuid = ArchCurrCpuid();
#endif

#ifndef USECBMC
    while (baseBitmap) {
        UINT32 basePrio = CLZ(baseBitmap) - 20; // 因为我们把优先级的位数从32减少到12
        HPFQueue *queueList = &rq->queueList[basePrio];
        UINT32 bitmap = queueList->queueBitmap;
        while (bitmap) {
            UINT32 priority = CLZ(bitmap) - 20; // 因为我们把优先级的位数从32减少到12
            LOS_DL_LIST_FOR_EACH_ENTRY(newTask, &queueList->priQueList[priority], LosTaskCB, pendList) {
#ifdef LOSCFG_KERNEL_SCHED_PLIMIT
                if (!OsSchedLimitCheckTime(newTask)) {
                    bitmap &= ~(1U << (OS_PRIORITY_QUEUE_NUM - priority - 1));
                    continue;
                }
#endif
#ifdef LOSCFG_KERNEL_SMP
                if (newTask->cpuAffiMask & (1U << cpuid)) {
#endif
                    return newTask;
#ifdef LOSCFG_KERNEL_SMP
                }
#endif
            }
            bitmap &= ~(1U << (OS_PRIORITY_QUEUE_NUM - priority - 1));
        }
        baseBitmap &= ~(1U << (OS_PRIORITY_QUEUE_NUM - basePrio - 1));
    }
#else // 增加对bitmap的信任度，改写while循环，减少状态空间
    if (baseBitmap) {
        UINT32 basePrio = CLZ(baseBitmap) - 20; // 因为我们把优先级的位数从32减少到12
        HPFQueue *queueList = &rq->queueList[basePrio];
        UINT32 bitmap = queueList->queueBitmap;
        if (bitmap) {
            UINT32 priority = CLZ(bitmap) - 20; // 因为我们把优先级的位数从32减少到12

            if (priority != OS_TASK_PRIORITY_HIGHEST){
                for(int i = priority - 1; i >= 0; i --){
                    __CPROVER_assert(LOS_ListEmpty(&queueList->priQueList[i]), "VR8: 如果调度策略为优先级策略，那么下一个任务是调度队列里面具有最高优先级的任务");
                }
            }

            LOS_DL_LIST_FOR_EACH_ENTRY(newTask, &queueList->priQueList[priority], LosTaskCB, pendList) {
                return newTask;
            }
        }
    }
#endif // USECBMC

    return NULL;
}

VOID EDFProcessDefaultSchedParamGet(SchedParam *param);
VOID EDFSchedPolicyInit(SchedRunqueue *rq);
UINT32 EDFTaskSchedParamInit(LosTaskCB *taskCB, UINT16 policy,
                             const SchedParam *parentParam,
                             const LosSchedParam *param);

VOID HPFSchedPolicyInit(SchedRunqueue *rq);
VOID HPFTaskSchedParamInit(LosTaskCB *taskCB, UINT16 policy,
                           const SchedParam *parentParam,
                           const LosSchedParam *param);
VOID HPFProcessDefaultSchedParamGet(SchedParam *param);

VOID IdleTaskSchedParamInit(LosTaskCB *taskCB);

INT32 OsSchedParamCompare(const LosTaskCB *task1, const LosTaskCB *task2);
VOID OsSchedPriorityInheritance(LosTaskCB *owner, const SchedParam *param);
UINT32 OsSchedParamInit(LosTaskCB *taskCB, UINT16 policy,
                        const SchedParam *parentParam,
                        const LosSchedParam *param);
VOID OsSchedProcessDefaultSchedParamGet(UINT16 policy, SchedParam *param);

VOID OsSchedResponseTimeReset(UINT64 responseTime);
VOID OsSchedToUserReleaseLock(VOID);
VOID OsSchedTick(VOID);
UINT32 OsSchedInit(VOID);
VOID OsSchedStart(VOID);

VOID OsSchedRunqueueIdleInit(LosTaskCB *idleTask);
VOID OsSchedRunqueueInit(VOID);

/*
 * This function simply picks the next task and switches to it.
 * Current task needs to already be in the right state or the right
 * queues it needs to be in.
 */
VOID OsSchedResched(VOID);
VOID OsSchedIrqEndCheckNeedSched(VOID);

/*
* This function inserts the runTask to the lock pending list based on the
* task priority.
*/
LOS_DL_LIST *OsSchedLockPendFindPos(const LosTaskCB *runTask, LOS_DL_LIST *lockList);

#ifdef __cplusplus
#if __cplusplus
}
#endif /* __cplusplus */
#endif /* __cplusplus */

#endif /* _LOS_SCHED_PRI_H */
