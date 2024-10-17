#include "los_sched_pri.h"
#include "los_task_pri.h"

STATIC EDFRunqueue g_schedEDF;

STATIC VOID EDFDequeue(SchedRunqueue *rq, LosTaskCB *taskCB);
STATIC VOID EDFEnqueue(SchedRunqueue *rq, LosTaskCB *taskCB);
STATIC UINT64 EDFWaitTimeGet(LosTaskCB *taskCB);
// STATIC UINT32 EDFWait(LosTaskCB *runTask, LOS_DL_LIST *list, UINT32 ticks);
// STATIC VOID EDFWake(LosTaskCB *resumedTask);
// STATIC BOOL EDFSchedParamModify(LosTaskCB *taskCB, const SchedParam *param);
// STATIC UINT32 EDFSchedParamGet(const LosTaskCB *taskCB, SchedParam *param);
// STATIC UINT32 EDFDelay(LosTaskCB *runTask, UINT64 waitTime);
// STATIC VOID EDFYield(LosTaskCB *runTask);
// STATIC VOID EDFExit(LosTaskCB *taskCB);
// STATIC UINT32 EDFSuspend(LosTaskCB *taskCB);
// STATIC UINT32 EDFResume(LosTaskCB *taskCB, BOOL *needSched);
STATIC UINT64 EDFTimeSliceGet(const LosTaskCB *taskCB);
STATIC VOID EDFTimeSliceUpdate(SchedRunqueue *rq, LosTaskCB *taskCB, UINT64 currTime);
STATIC INT32 EDFParamCompare(const SchedPolicy *sp1, const SchedPolicy *sp2);
// STATIC VOID EDFPriorityInheritance(LosTaskCB *owner, const SchedParam *param);
// STATIC VOID EDFPriorityRestore(LosTaskCB *owner, const LOS_DL_LIST *list, const SchedParam *param);

const STATIC SchedOps g_deadlineOps = {
    .dequeue = EDFDequeue,
    .enqueue = EDFEnqueue,
    .waitTimeGet = EDFWaitTimeGet,
    // .wait = EDFWait,
    // .wake = EDFWake,
    // .schedParamModify = EDFSchedParamModify,
    // .schedParamGet = EDFSchedParamGet,
    // .delay = EDFDelay,
    // .yield = EDFYield,
    .start = EDFDequeue,
    // .exit = EDFExit,
    // .suspend = EDFSuspend,
    // .resume = EDFResume,
    .deadlineGet = EDFTimeSliceGet,
    .timeSliceUpdate = EDFTimeSliceUpdate,
    // .schedParamCompare = EDFParamCompare,
    // .priorityInheritance = EDFPriorityInheritance,
    // .priorityRestore = EDFPriorityRestore,
};

STATIC VOID EDFTimeSliceUpdate(SchedRunqueue *rq, LosTaskCB *taskCB, UINT64 currTime)
{
    SchedEDF *sched = (SchedEDF *)&taskCB->sp;

#ifdef USECBMC
    __CPROVER_assert(currTime >= taskCB->startTime, "当前时间大于任务开始时间");
#endif

    if (taskCB->timeSlice <= 0) {
        taskCB->irqUsedTime = 0;
        return;
    }

    INT32 incTime = (currTime - taskCB->startTime - taskCB->irqUsedTime);

#ifdef USECBMC
    __CPROVER_assert(incTime >= 0, "任务的运行时间大于0");
#endif

#ifdef LOSCFG_SCHED_EDF_DEBUG
    taskCB->schedStat.timeSliceRealTime += incTime;
    taskCB->schedStat.allRuntime += (currTime - taskCB->startTime);
#endif

    taskCB->timeSlice -= incTime;
    taskCB->irqUsedTime = 0;
    taskCB->startTime = currTime;

    if ((sched->finishTime > currTime) && (taskCB->timeSlice > 0)) {
        return;
    }

    rq->schedFlag |= INT_PEND_RESCH;
    if (sched->finishTime <= currTime) {
#ifdef LOSCFG_SCHED_EDF_DEBUG
        EDFDebugRecord((UINTPTR *)taskCB, sched->finishTime);
#endif

        taskCB->timeSlice = 0;
        // PrintExcInfo("EDF task %u is timeout, runTime: %d us period: %llu us\n", taskCB->taskID,
        //              (INT32)OS_SYS_CYCLE_TO_US((UINT64)sched->runTime), OS_SYS_CYCLE_TO_US(sched->period));
    }
}

STATIC UINT64 EDFTimeSliceGet(const LosTaskCB *taskCB)
{
    SchedEDF *sched = (SchedEDF *)&taskCB->sp;
    UINT64 endTime = taskCB->startTime + taskCB->timeSlice;
    return (endTime > sched->finishTime) ? sched->finishTime : endTime;
}

STATIC VOID DeadlineQueueInsert(EDFRunqueue *rq, LosTaskCB *taskCB)
{
    LOS_DL_LIST *root = &rq->root;
    if (LOS_ListEmpty(root)) {
        LOS_ListTailInsert(root, &taskCB->pendList);
        return;
    }

    LOS_DL_LIST *list = root->pstNext;
    do {
        LosTaskCB *readyTask = LOS_DL_LIST_ENTRY(list, LosTaskCB, pendList);
        if (EDFParamCompare(&readyTask->sp, &taskCB->sp) > 0) {
            LOS_ListHeadInsert(list, &taskCB->pendList);
            return;
        }
        list = list->pstNext;
    } while (list != root);

    LOS_ListHeadInsert(list, &taskCB->pendList);
}

STATIC VOID EDFEnqueue(SchedRunqueue *rq, LosTaskCB *taskCB)
{
#ifdef USECBMC
    __CPROVER_assert(!(taskCB->taskStatus & OS_TASK_STATUS_READY), "任务状态不为就绪态");
#endif

    EDFRunqueue *erq = rq->edfRunqueue;
    SchedEDF *sched = (SchedEDF *)&taskCB->sp;
    if (taskCB->timeSlice <= 0) { // 任务的时间片用完了
#ifdef LOSCFG_SCHED_EDF_DEBUG
        UINT64 oldFinish = sched->finishTime;
#endif
        UINT64 currTime = OsGetCurrSchedTimeCycle();
        if (sched->flags == EDF_INIT) { // 初始调度周期
            sched->finishTime = currTime;
        } else if (sched->flags != EDF_NEXT_PERIOD) { // EDF_UNUSED、EDF_WAIT_FOREVER
            /* The start time of the next period */
            sched->finishTime = (sched->finishTime - sched->deadline) + sched->period;
        }

        /* Calculate the start time of the next period */

#ifdef USECBMC
        // 添加退出逻辑，防止cbmc卡死
        int counter = 0;
        UINT64 temp = sched->finishTime; 

#endif
        while (1) { 
            /* The deadline of the next period */
            UINT64 finishTime = sched->finishTime + sched->deadline;
            if ((finishTime <= currTime) || ((sched->finishTime + sched->runTime) > finishTime)) {
                /* This period cannot meet the minimum running time, so it is migrated to the next period */
                sched->finishTime += sched->period;
#ifdef USECBMC
                __CPROVER_assert(sched->finishTime > temp, "任务的完成时间递增");
                temp = sched->finishTime;
                counter ++;

                if (counter >= 5) // 如果连续5次循环sched->finishTime都在递增，说明退出是迟早的事情，这边手动退出
                {
                    sched->finishTime = currTime; // 循环退出条件之一
                    break;
                }            
#endif
                continue;
            }
            break;
        }

        if (sched->finishTime > currTime) {
            /* Wait for the next period to start */
            LOS_ListTailInsert(&erq->waitList, &taskCB->pendList);
            taskCB->waitTime = OS_SCHED_MAX_RESPONSE_TIME;
            if (!OsTaskIsRunning(taskCB)) {
                OsSchedTimeoutQueueAdd(taskCB, sched->finishTime);
            }
#ifdef LOSCFG_SCHED_EDF_DEBUG
            if (oldFinish != sched->finishTime) {
                EDFDebugRecord((UINTPTR *)taskCB, oldFinish);
                taskCB->schedStat.allRuntime = 0;
                taskCB->schedStat.timeSliceRealTime = 0;
                taskCB->schedStat.pendTime = 0;
            }
#endif
            taskCB->taskStatus |= OS_TASK_STATUS_PEND_TIME;
            sched->flags = EDF_NEXT_PERIOD;
            return;
        }

        sched->finishTime += sched->deadline;
        taskCB->timeSlice = sched->runTime;
        sched->flags = EDF_UNUSED;
    }

    DeadlineQueueInsert(erq, taskCB);
    taskCB->taskStatus &= ~(OS_TASK_STATUS_BLOCKED | OS_TASK_STATUS_TIMEOUT);
    taskCB->taskStatus |= OS_TASK_STATUS_READY;
}

STATIC VOID EDFDequeue(SchedRunqueue *rq, LosTaskCB *taskCB)
{
    (VOID)rq;
    LOS_ListDelete(&taskCB->pendList);
    taskCB->taskStatus &= ~OS_TASK_STATUS_READY;
}

STATIC UINT64 EDFWaitTimeGet(LosTaskCB *taskCB)
{
    const SchedEDF *sched = (const SchedEDF *)&taskCB->sp;
    if (sched->flags != EDF_WAIT_FOREVER) {
        taskCB->waitTime += taskCB->startTime;
    }
    return (taskCB->waitTime >= sched->finishTime) ? sched->finishTime : taskCB->waitTime;
}

STATIC INT32 EDFParamCompare(const SchedPolicy *sp1, const SchedPolicy *sp2)
{
    const SchedEDF *param1 = (const SchedEDF *)sp1;
    const SchedEDF *param2 = (const SchedEDF *)sp2;

    return (INT32)(param1->finishTime - param2->finishTime);
}

UINT32 EDFTaskSchedParamInit(LosTaskCB *taskCB, UINT16 policy,
                             const SchedParam *parentParam,
                             const LosSchedParam *param)
{
    (VOID)parentParam;
    SchedEDF *sched = (SchedEDF *)&taskCB->sp;
    sched->flags = EDF_INIT;
    sched->policy = policy;
    sched->runTime = (INT32)OS_SYS_US_TO_CYCLE((UINT64)param->runTimeUs);
    sched->deadline = OS_SYS_US_TO_CYCLE(param->deadlineUs);
    sched->period = OS_SYS_US_TO_CYCLE(param->periodUs);
    sched->finishTime = 0;
    taskCB->timeSlice = 0;
    taskCB->ops = &g_deadlineOps;
    return LOS_OK;
}

VOID EDFSchedPolicyInit(SchedRunqueue *rq)
{
    if (ArchCurrCpuid() > 0) {
        rq->edfRunqueue = &g_schedEDF;
        return;
    }

    EDFRunqueue *erq = &g_schedEDF;
    erq->period = OS_SCHED_MAX_RESPONSE_TIME;
    LOS_ListInit(&erq->root);
    LOS_ListInit(&erq->waitList);
    rq->edfRunqueue = erq;
}