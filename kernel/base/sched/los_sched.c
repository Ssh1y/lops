#include "los_sched_pri.h"
#include "los_task_pri.h"

UINT32 nondet_uint32();
SchedRunqueue g_schedRunqueue[LOSCFG_KERNEL_CORE_NUM];

// for compile
LosTaskCB *g_runTask;

STATIC INLINE VOID SchedNextExpireTimeSet(UINT32 responseID, UINT64 taskEndTime, UINT32 oldResponseID)
{
    SchedRunqueue *rq = OsSchedRunqueue();
    BOOL isTimeSlice = FALSE;
    UINT64 currTime = OsGetCurrSchedTimeCycle();
    UINT64 nextExpireTime = OsGetSortLinkNextExpireTime(&rq->timeoutQueue, currTime, OS_TICK_RESPONSE_PRECISION);

    rq->schedFlag &= ~INT_PEND_TICK;
    if (rq->responseID == oldResponseID) {
        /* This time has expired, and the next time the theory has expired is infinite */
        rq->responseTime = OS_SCHED_MAX_RESPONSE_TIME;
    }

    /* The current thread's time slice has been consumed, but the current system lock task cannot
     * trigger the schedule to release the CPU
     */
    if ((nextExpireTime > taskEndTime) && ((nextExpireTime - taskEndTime) > OS_SCHED_MINI_PERIOD)) {
        nextExpireTime = taskEndTime;
        isTimeSlice = TRUE;
    }

    if ((rq->responseTime <= nextExpireTime) ||
        ((rq->responseTime - nextExpireTime) < OS_TICK_RESPONSE_PRECISION)) {
        return;
    }

    if (isTimeSlice) {
        /* The expiration time of the current system is the thread's slice expiration time */
        rq->responseID = responseID;
    } else {
        rq->responseID = OS_INVALID_VALUE;
    }

    UINT64 nextResponseTime = nextExpireTime - currTime;
    // rq->responseTime = currTime + HalClockTickTimerReload(nextResponseTime);
    rq->responseTime = currTime + nextResponseTime; // 忽略定时器
}

VOID OsSchedRunqueueInit(VOID)
{
    if (ArchCurrCpuid() != 0) {
        return;
    }

    for (UINT16 index = 0; index < LOSCFG_KERNEL_CORE_NUM; index++) {
        SchedRunqueue *rq = OsSchedRunqueueByID(index);
        OsSortLinkInit(&rq->timeoutQueue);
        rq->responseTime = OS_SCHED_MAX_RESPONSE_TIME;
    }
}

VOID OsSchedRunqueueIdleInit(LosTaskCB *idleTask)
{
    SchedRunqueue *rq = OsSchedRunqueue();
    rq->idleTask = idleTask;
}

UINT32 OsSchedInit(VOID)
{
    for (UINT16 cpuid = 0; cpuid < LOSCFG_KERNEL_CORE_NUM; cpuid++) {
        SchedRunqueue *rq = OsSchedRunqueueByID(cpuid);
        EDFSchedPolicyInit(rq);
        HPFSchedPolicyInit(rq);

        // for compile, init
        rq->idleTask = NULL;
        rq->taskLockCnt = 0;
    }

#ifdef LOSCFG_SCHED_TICK_DEBUG
    UINT32 ret = OsSchedDebugInit();
    if (ret != LOS_OK) {
        return ret;
    }
#endif
    return LOS_OK;
}

UINT32 OsSchedParamInit(LosTaskCB *taskCB, UINT16 policy, const SchedParam *parentParam, const LosSchedParam *param)
{
    switch (policy) {
        case LOS_SCHED_FIFO:
        case LOS_SCHED_RR:
            HPFTaskSchedParamInit(taskCB, policy, parentParam, param);
            break;
        case LOS_SCHED_DEADLINE:
            return EDFTaskSchedParamInit(taskCB, policy, parentParam, param);
        case LOS_SCHED_IDLE:
            // IdleTaskSchedParamInit(taskCB); // 暂时不考虑idle任务
            break;
        default:
            return LOS_NOK;
    }

    return LOS_OK;
}

STATIC LosTaskCB *TopTaskGet(SchedRunqueue *rq)
{
    LosTaskCB *newTask = EDFRunqueueTopTaskGet(rq->edfRunqueue);
    if (newTask != NULL) {
        goto FIND;
    }

    newTask = HPFRunqueueTopTaskGet(rq->hpfRunqueue);
    if (newTask != NULL) {
        goto FIND;
    }

#ifdef USECBMC
    __CPROVER_assert(newTask == NULL, "VR10：若调度时没有任务准备好，那么下一个被调度的任务是调度队列中的空闲任务");
#endif
    newTask = rq->idleTask;

FIND:

    // 
    if (newTask == NULL) {
        return NULL;
    }

    // newTask->ops->start(rq, newTask); //todo 单独验证dequeue操作
    // 更换为
    newTask->taskStatus &= ~OS_TASK_STATUS_READY; // 任务去除就绪状态
    return newTask;
}

STATIC VOID SchedTaskSwitch(SchedRunqueue *rq, LosTaskCB *runTask, LosTaskCB *newTask)
{
    // SchedSwitchCheck(runTask, newTask); // 没什么用

    runTask->taskStatus &= ~OS_TASK_STATUS_RUNNING;
    newTask->taskStatus |= OS_TASK_STATUS_RUNNING;

#ifdef LOSCFG_KERNEL_SMP
    /* mask new running task's owner processor */
    runTask->currCpu = OS_TASK_INVALID_CPUID;
    newTask->currCpu = ArchCurrCpuid();
#endif

    OsCurrTaskSet((VOID *)newTask);
#ifdef LOSCFG_KERNEL_VM
    if (newTask->archMmu != runTask->archMmu) {
        LOS_ArchMmuContextSwitch((LosArchMmu *)newTask->archMmu);
    }
#endif

#ifdef LOSCFG_KERNEL_CPUP
    OsCpupCycleEndStart(runTask, newTask);
#endif

#ifdef LOSCFG_SCHED_HPF_DEBUG
    UINT64 waitStartTime = newTask->startTime;
#endif
    if (runTask->taskStatus & OS_TASK_STATUS_READY) {
        /* When a thread enters the ready queue, its slice of time is updated */
        newTask->startTime = runTask->startTime;
    } else {
        // /* The currently running task is blocked */
        // newTask->startTime = OsGetCurrSchedTimeCycle();
        // /* The task is in a blocking state and needs to update its time slice before pend */
        // runTask->ops->timeSliceUpdate(rq, runTask, newTask->startTime);

        // if (runTask->taskStatus & (OS_TASK_STATUS_PEND_TIME | OS_TASK_STATUS_DELAY)) { // block
        //     OsSchedTimeoutQueueAdd(runTask, runTask->ops->waitTimeGet(runTask));
        // }
    }

    // UINT64 deadline = newTask->ops->deadlineGet(newTask);
    // SchedNextExpireTimeSet(newTask->taskID, deadline, runTask->taskID);

#ifdef LOSCFG_SCHED_HPF_DEBUG
    newTask->schedStat.waitSchedTime += newTask->startTime - waitStartTime;
    newTask->schedStat.waitSchedCount++;
    runTask->schedStat.runTime = runTask->schedStat.allRuntime;
    runTask->schedStat.switchCount++;
#endif
    /* do the task context switch */
    // OsTaskSchedule(newTask, runTask);
}

VOID OsSchedResched(VOID)
{
    // LOS_ASSERT(LOS_SpinHeld(&g_taskSpin));
    SchedRunqueue *rq = OsSchedRunqueue();
#ifdef LOSCFG_KERNEL_SMP
    LOS_ASSERT(rq->taskLockCnt == 1);
#else
#ifdef USECBMC
    __CPROVER_assert(rq->taskLockCnt == 0, "调度队列的任务锁计数为0");
#endif /* USECBMC */
#endif

    rq->schedFlag &= ~INT_PEND_RESCH;
    LosTaskCB *runTask = OsCurrTaskGet();
    LosTaskCB *newTask = TopTaskGet(rq);

    if (runTask->sp.edf.policy){
#ifdef USECBMC
        __CPROVER_assert(runTask->sp.edf.finishTime >= newTask->sp.edf.finishTime, "VR9：如果调度策略为最早截止时间优先调度策略，那么下一个任务是调度队列中具有最早截止时间的任务");
#endif
    }

    if (runTask == newTask) {
        return;
    }

    SchedTaskSwitch(rq, runTask, newTask);

#ifdef USECBMC
    __CPROVER_assert(newTask->taskStatus & OS_TASK_STATUS_RUNNING, "VR11：调度结束之后，被调度的任务的状态从Ready更改为Running");
    __CPROVER_assert(!(runTask->taskStatus & OS_TASK_STATUS_RUNNING) && (runTask->taskStatus & OS_TASK_STATUS_READY) , "VR12: 调度结束之后，调度前的当前运行任务去除Running状态");
#endif
}

VOID LOS_Schedule(VOID)
{
    UINT32 intSave;
    LosTaskCB *runTask = OsCurrTaskGet();
    SchedRunqueue *rq = OsSchedRunqueue();

#ifdef USECBMC
    __CPROVER_assert(rq != NULL, "VR7：调度前当前运行的任务不为空");
#endif

    UINT32 Os_Int_Active;
// #ifdef USECBMC
//     Os_Int_Active = nondet_uint32();
//     __CPROVER_assume(Os_Int_Active == 0 || Os_Int_Active == 1);
// #else
    Os_Int_Active = 0;
// #endif

    if (Os_Int_Active) {
        OsSchedRunqueuePendingSet();
        return;
    }

    if (!OsPreemptable()) {
        return;
    }

#ifdef USECBMC
    __CPROVER_assert(OsPreemptable() == TRUE, "VR6: 若调度队列不允许抢占，则放弃调度");
#endif

    /*
     * trigger schedule in task will also do the slice check
     * if necessary, it will give up the timeslice more in time.
     * otherwise, there's no other side effects.
     */
    // SCHEDULER_LOCK(intSave);

    runTask->ops->timeSliceUpdate(rq, runTask, OsGetCurrSchedTimeCycle());

    /* add run task back to ready queue */
    runTask->ops->enqueue(rq, runTask);

    /* reschedule to new thread */
    OsSchedResched();

    // SCHEDULER_UNLOCK(intSave);
}