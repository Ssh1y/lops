#include "los_task_pri.h"

UINT16 nondet_ushort();
UINT32 nondet_uint();
LITE_OS_SEC_TEXT_INIT UINT32 createTask(UINT16 policy) // 创建任务并加入就绪队列
{
    UINT32 taskID;
    TSK_INIT_PARAM_S taskInitParam = {0};

    taskInitParam.policy = policy;
#ifdef USECBMC

    if (taskInitParam.policy == LOS_SCHED_RR || taskInitParam.policy == LOS_SCHED_FIFO || taskInitParam.policy == LOS_SCHED_NORMAL)
    {
        taskInitParam.usTaskPrio = nondet_ushort();
        __CPROVER_assume(taskInitParam.usTaskPrio >= 0 && taskInitParam.usTaskPrio <= OS_TASK_PRIORITY_LOWEST);
    }
    else if (taskInitParam.policy == LOS_SCHED_DEADLINE)
    {
        taskInitParam.runTimeUs = 500;
        taskInitParam.deadlineUs = nondet_uint();
        taskInitParam.periodUs = 4000;

        __CPROVER_assume(taskInitParam.deadlineUs > taskInitParam.runTimeUs && taskInitParam.deadlineUs < taskInitParam.periodUs);
    }

#else // for gcc
    taskInitParam.runTimeUs = 500;
    taskInitParam.deadlineUs = 2500;
    taskInitParam.periodUs = 4000;
#endif
    LOS_TaskCreate(&taskID, &taskInitParam);
    return taskID;
}

LITE_OS_SEC_TEXT_INIT UINT32 createTaskOnly(UINT16 policy) // 创建任务但不加入就绪队列
{
    UINT32 taskID;
    TSK_INIT_PARAM_S taskInitParam = {0};

    taskInitParam.policy = policy;
#ifdef USECBMC

    if (taskInitParam.policy == LOS_SCHED_RR || taskInitParam.policy == LOS_SCHED_FIFO || taskInitParam.policy == LOS_SCHED_NORMAL)
    {
        taskInitParam.usTaskPrio = nondet_ushort();
        __CPROVER_assume(taskInitParam.usTaskPrio >= 0 && taskInitParam.usTaskPrio <= OS_TASK_PRIORITY_LOWEST); /* code */
    }
    else if (taskInitParam.policy == LOS_SCHED_DEADLINE)
    {
        taskInitParam.runTimeUs = 1000;
        taskInitParam.deadlineUs = nondet_uint();
        taskInitParam.periodUs = 3000;

        __CPROVER_assume(taskInitParam.deadlineUs > taskInitParam.runTimeUs && taskInitParam.deadlineUs < taskInitParam.periodUs);
    }

#else // for gcc
    // taskInitParam.usTaskPrio = 10;
    taskInitParam.runTimeUs = 1000;
    taskInitParam.deadlineUs = 2000;
    taskInitParam.periodUs = 3000;
#endif
    LOS_TaskCreateOnly(&taskID, &taskInitParam);
    return taskID;
}

LITE_OS_SEC_TEXT_INIT UINT32 OsMain(VOID)
{
    UINTPTR processCB = 0;

    OsSchedRunqueueInit();        // 初始化调度队列的超时队列
    return OsTaskInit(processCB); // 初始化调度队列和任务链表
}

LITE_OS_SEC_TEXT_INIT INT32 main(VOID)
{
    OsMain();

    // 可以使用cbmc非确定性建模，但是对整个项目的状态空间太大，所以这里使用确定值
    // UINT16 policy = LOS_SCHED_RR; // 对应HPF调度策略
    UINT16 policy = LOS_SCHED_DEADLINE; // 对应EDF调度策略


    UINT32 taskID0 = createTaskOnly(policy); // 创建一个任务但不加入就绪队列，作为当前运行任务
    UINT32 taskID1 = createTask(policy);
    LosTaskCB *taskCB0 = OS_TCB_FROM_TID(taskID0);
    LosTaskCB *taskCB1 = OS_TCB_FROM_TID(taskID1);

    OsCurrTaskSet(taskCB0); // 将该taskID0设置为运行任务
    LOS_Schedule(); // 调度
}