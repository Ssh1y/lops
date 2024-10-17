#include "los_sched_pri.h"
#include "los_task_pri.h"

#define OS_SCHED_FIFO_TIMEOUT      0x7FFFFFFF
// #define PRIQUEUE_PRIOR0_BIT        0x80000000U
#define PRIQUEUE_PRIOR0_BIT        0x800U // 修改了优先级之后相应修改这里
#define OS_SCHED_TIME_SLICES_MIN   ((5000 * OS_SYS_NS_PER_US) / OS_NS_PER_CYCLE)  /* 5ms */
#define OS_SCHED_TIME_SLICES_MAX   ((LOSCFG_BASE_CORE_TIMESLICE_TIMEOUT * OS_SYS_NS_PER_US) / OS_NS_PER_CYCLE)
#define OS_SCHED_TIME_SLICES_DIFF  (OS_SCHED_TIME_SLICES_MAX - OS_SCHED_TIME_SLICES_MIN)
#define OS_SCHED_READY_MAX         30
#define OS_TIME_SLICE_MIN          (INT32)((50 * OS_SYS_NS_PER_US) / OS_NS_PER_CYCLE) /* 50us */

STATIC HPFRunqueue g_schedHPF;

STATIC VOID HPFDequeue(SchedRunqueue *rq, LosTaskCB *taskCB);
STATIC VOID HPFEnqueue(SchedRunqueue *rq, LosTaskCB *taskCB);
STATIC UINT64 HPFWaitTimeGet(LosTaskCB *taskCB);
// STATIC UINT32 HPFWait(LosTaskCB *runTask, LOS_DL_LIST *list, UINT32 ticks);
// STATIC VOID HPFWake(LosTaskCB *resumedTask);
// STATIC BOOL HPFSchedParamModify(LosTaskCB *taskCB, const SchedParam *param);
// STATIC UINT32 HPFSchedParamGet(const LosTaskCB *taskCB, SchedParam *param);
// STATIC UINT32 HPFDelay(LosTaskCB *runTask, UINT64 waitTime);
// STATIC VOID HPFYield(LosTaskCB *runTask);
STATIC VOID HPFStartToRun(SchedRunqueue *rq, LosTaskCB *taskCB);
// STATIC VOID HPFExit(LosTaskCB *taskCB);
// STATIC UINT32 HPFSuspend(LosTaskCB *taskCB);
// STATIC UINT32 HPFResume(LosTaskCB *taskCB, BOOL *needSched);
STATIC UINT64 HPFTimeSliceGet(const LosTaskCB *taskCB);
STATIC VOID HPFTimeSliceUpdate(SchedRunqueue *rq, LosTaskCB *taskCB, UINT64 currTime);
// STATIC INT32 HPFParamCompare(const SchedPolicy *sp1, const SchedPolicy *sp2);
// STATIC VOID HPFPriorityInheritance(LosTaskCB *owner, const SchedParam *param);
// STATIC VOID HPFPriorityRestore(LosTaskCB *owner, const LOS_DL_LIST *list, const SchedParam *param);

const STATIC SchedOps g_priorityOps = {
    .dequeue = HPFDequeue,
    .enqueue = HPFEnqueue,
    .waitTimeGet = HPFWaitTimeGet,
    // .wait = HPFWait,
    // .wake = HPFWake,
    // .schedParamModify = HPFSchedParamModify,
    // .schedParamGet = HPFSchedParamGet,
    // .delay = HPFDelay,
    // .yield = HPFYield,
    .start = HPFStartToRun,
    // .exit = HPFExit,
    // .suspend = HPFSuspend,
    // .resume = HPFResume,
    .deadlineGet = HPFTimeSliceGet,
    .timeSliceUpdate = HPFTimeSliceUpdate,
    // .schedParamCompare = HPFParamCompare,
    // .priorityInheritance = HPFPriorityInheritance,
    // .priorityRestore = HPFPriorityRestore,
};

UINT16 nondet_ushort();
STATIC VOID HPFTimeSliceUpdate(SchedRunqueue *rq, LosTaskCB *taskCB, UINT64 currTime)
{
    SchedHPF *sched = (SchedHPF *)&taskCB->sp;

#ifdef USECBMC
    __CPROVER_assert(currTime >= taskCB->startTime, "当前时间大于任务开始时间");
#endif

    INT32 incTime = (currTime - taskCB->startTime - taskCB->irqUsedTime);

#ifdef USECBMC
    __CPROVER_assert(incTime >= 0, "任务的运行时间大于0");
#endif

    if (sched->policy == LOS_SCHED_RR) {
        taskCB->timeSlice -= incTime;
#ifdef LOSCFG_SCHED_HPF_DEBUG
        taskCB->schedStat.timeSliceRealTime += incTime;
#endif
    }
#ifdef LOSCFG_KERNEL_SCHED_PLIMIT
    OsSchedLimitUpdateRuntime(taskCB, currTime, incTime);
#endif
    taskCB->irqUsedTime = 0;
    taskCB->startTime = currTime;
    if (taskCB->timeSlice <= OS_TIME_SLICE_MIN) {
        rq->schedFlag |= INT_PEND_RESCH;
    }

#ifdef LOSCFG_SCHED_HPF_DEBUG
    taskCB->schedStat.allRuntime += incTime;
#endif
}

STATIC UINT64 HPFTimeSliceGet(const LosTaskCB *taskCB)
{
    SchedHPF *sched = (SchedHPF *)&taskCB->sp;
    INT32 timeSlice = taskCB->timeSlice;

    timeSlice = (timeSlice <= OS_TIME_SLICE_MIN) ? sched->initTimeSlice : timeSlice;
    return (taskCB->startTime + timeSlice);
}


STATIC INLINE UINT32 TimeSliceCalculate(HPFRunqueue *rq, UINT16 basePrio, UINT16 priority)
{
    UINT32 time;
    UINT32 readyTasks;

    HPFQueue *queueList = &rq->queueList[basePrio];
    readyTasks = queueList->readyTasks[priority];
    if (readyTasks > OS_SCHED_READY_MAX) {
        return OS_SCHED_TIME_SLICES_MIN;
    }
    time = ((OS_SCHED_READY_MAX - readyTasks) * OS_SCHED_TIME_SLICES_DIFF) / OS_SCHED_READY_MAX;
    return (time + OS_SCHED_TIME_SLICES_MIN);
}

STATIC INLINE VOID PriQueHeadInsert(HPFRunqueue *rq, UINT32 basePrio, LOS_DL_LIST *priQue, UINT32 priority)
{
    HPFQueue *queueList = &rq->queueList[basePrio];
    LOS_DL_LIST *priQueList = &queueList->priQueList[0];
    UINT32 *bitmap = &queueList->queueBitmap;

    /*
     * Task control blocks are inited as zero. And when task is deleted,
     * and at the same time would be deleted from priority queue or
     * other lists, task pend node will restored as zero.
     */
#ifdef USECBMC
    __CPROVER_assert(priQue->pstNext == NULL, "调度队列已初始化");
#endif

    if (*bitmap == 0) {
        rq->queueBitmap |= PRIQUEUE_PRIOR0_BIT >> basePrio;
    }

    if (LOS_ListEmpty(&priQueList[priority])) {
        *bitmap |= PRIQUEUE_PRIOR0_BIT >> priority;
    }

    LOS_ListHeadInsert(&priQueList[priority], priQue);
    queueList->readyTasks[priority]++;
}

STATIC INLINE VOID PriQueTailInsert(HPFRunqueue *rq, UINT32 basePrio, LOS_DL_LIST *priQue, UINT32 priority)
{
    HPFQueue *queueList = &rq->queueList[basePrio];
    LOS_DL_LIST *priQueList = &queueList->priQueList[0];
    UINT32 *bitmap = &queueList->queueBitmap;

    /*
     * Task control blocks are inited as zero. And when task is deleted,
     * and at the same time would be deleted from priority queue or
     * other lists, task pend node will restored as zero.
     */
#ifdef USECBMC
    __CPROVER_assert(priQue->pstNext == NULL, "调度队列已初始化");
#endif
    if (*bitmap == 0) {
        rq->queueBitmap |= PRIQUEUE_PRIOR0_BIT >> basePrio;
    }

    if (LOS_ListEmpty(&priQueList[priority])) {
        *bitmap |= PRIQUEUE_PRIOR0_BIT >> priority;
    }

    LOS_ListTailInsert(&priQueList[priority], priQue);
    queueList->readyTasks[priority]++;
}

STATIC INLINE VOID PriQueDelete(HPFRunqueue *rq, UINT32 basePrio, LOS_DL_LIST *priQue, UINT32 priority)
{
    HPFQueue *queueList = &rq->queueList[basePrio];
    LOS_DL_LIST *priQueList = &queueList->priQueList[0];
    UINT32 *bitmap = &queueList->queueBitmap;

    LOS_ListDelete(priQue);
    queueList->readyTasks[priority]--;
    if (LOS_ListEmpty(&priQueList[priority])) {
        *bitmap &= ~(PRIQUEUE_PRIOR0_BIT >> priority);
    }

    if (*bitmap == 0) {
        rq->queueBitmap &= ~(PRIQUEUE_PRIOR0_BIT >> basePrio);
    }
}

STATIC INLINE VOID PriQueInsert(HPFRunqueue *rq, LosTaskCB *taskCB)
{
#ifdef USECBMC
    __CPROVER_assert(!(taskCB->taskStatus & OS_TASK_STATUS_READY), "任务状态不为就绪态");
#endif
    SchedHPF *sched = (SchedHPF *)&taskCB->sp;

    switch (sched->policy) {
        case LOS_SCHED_RR: {
            if (taskCB->timeSlice > OS_TIME_SLICE_MIN) {
                PriQueHeadInsert(rq, sched->basePrio, &taskCB->pendList, sched->priority);
            } else {
                sched->initTimeSlice = TimeSliceCalculate(rq, sched->basePrio, sched->priority);
                taskCB->timeSlice = sched->initTimeSlice;
                PriQueTailInsert(rq, sched->basePrio, &taskCB->pendList, sched->priority);
#ifdef LOSCFG_SCHED_HPF_DEBUG
                taskCB->schedStat.timeSliceTime = taskCB->schedStat.timeSliceRealTime;
                taskCB->schedStat.timeSliceCount++;
#endif
            }
            break;
        }
        case LOS_SCHED_FIFO: {
            /* The time slice of FIFO is always greater than 0 unless the yield is called */
            if ((taskCB->timeSlice > OS_TIME_SLICE_MIN) && (taskCB->taskStatus & OS_TASK_STATUS_RUNNING)) {
                PriQueHeadInsert(rq, sched->basePrio, &taskCB->pendList, sched->priority);
            } else {
                sched->initTimeSlice = OS_SCHED_FIFO_TIMEOUT;
                taskCB->timeSlice = sched->initTimeSlice;
                PriQueTailInsert(rq, sched->basePrio, &taskCB->pendList, sched->priority);
            }
            break;
        }
        default:
#ifdef USECBMC
            __CPROVER_assert(0, "调度策略合法");
#endif
            break;
    }
    
    taskCB->taskStatus &= ~OS_TASK_STATUS_BLOCKED;
    taskCB->taskStatus |= OS_TASK_STATUS_READY;
}

STATIC VOID HPFEnqueue(SchedRunqueue *rq, LosTaskCB *taskCB)
{
#ifdef LOSCFG_SCHED_HPF_DEBUG
    if (!(taskCB->taskStatus & OS_TASK_STATUS_RUNNING)) {
        taskCB->startTime = OsGetCurrSchedTimeCycle();
    }
#endif
    PriQueInsert(rq->hpfRunqueue, taskCB);
}

STATIC VOID HPFDequeue(SchedRunqueue *rq, LosTaskCB *taskCB)
{
    SchedHPF *sched = (SchedHPF *)&taskCB->sp;

    if (taskCB->taskStatus & OS_TASK_STATUS_READY) {
        PriQueDelete(rq->hpfRunqueue, sched->basePrio, &taskCB->pendList, sched->priority);
        taskCB->taskStatus &= ~OS_TASK_STATUS_READY;
    }
}

STATIC VOID HPFStartToRun(SchedRunqueue *rq, LosTaskCB *taskCB)
{
    HPFDequeue(rq, taskCB);
}

STATIC UINT64 HPFWaitTimeGet(LosTaskCB *taskCB)
{
    taskCB->waitTime += taskCB->startTime;
    return taskCB->waitTime; // 更新任务的等待时间
}

VOID HPFTaskSchedParamInit(LosTaskCB *taskCB, UINT16 policy,
                           const SchedParam *parentParam,
                           const LosSchedParam *param)
{
    SchedHPF *sched = (SchedHPF *)&taskCB->sp;

    sched->policy = policy;
    if (param != NULL) {
        sched->priority = param->priority;
    } else {
        sched->priority = parentParam->priority;
    }
    // sched->basePrio = parentParam->basePrio; // 将进程优先级修改为cbmc建模的非确定值
#ifdef USECBMC
    sched->basePrio = nondet_ushort();
    __CPROVER_assume(sched->basePrio >= 0 && sched->basePrio <= OS_TASK_PRIORITY_LOWEST);
#else
    sched->basePrio = OS_TASK_PRIORITY_HIGHEST;
#endif

    sched->initTimeSlice = 0;
    taskCB->timeSlice = sched->initTimeSlice;
    taskCB->ops = &g_priorityOps;
}

VOID HPFSchedPolicyInit(SchedRunqueue *rq)
{
    if (ArchCurrCpuid() > 0) {
        rq->hpfRunqueue = &g_schedHPF;
        return;
    }

    for (UINT16 index = 0; index < OS_PRIORITY_QUEUE_NUM; index++) {
        HPFQueue *queueList = &g_schedHPF.queueList[index];
        LOS_DL_LIST *priQue = &queueList->priQueList[0];
        for (UINT16 prio = 0; prio < OS_PRIORITY_QUEUE_NUM; prio++) {
            LOS_ListInit(&priQue[prio]);
        }
    }

    rq->hpfRunqueue = &g_schedHPF;
}