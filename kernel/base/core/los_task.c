#include "los_task_pri.h"
#include "los_sched_pri.h"

#if (LOSCFG_BASE_CORE_TSK_LIMIT <= 0)
#error "task maxnum cannot be zero"
#endif  /* LOSCFG_BASE_CORE_TSK_LIMIT <= 0 */

LITE_OS_SEC_BSS LosTaskCB    *g_taskCBArray;
LITE_OS_SEC_BSS LOS_DL_LIST  g_losFreeTask;
LITE_OS_SEC_BSS LOS_DL_LIST  g_taskRecycleList;
LITE_OS_SEC_BSS UINT32       g_taskMaxNum;
LITE_OS_SEC_BSS UINT32       g_taskScheduled; /* one bit for each cores */

UINT32 nondet_uint32();
UINT32 OsTaskInit(UINTPTR processCB) // 初始化任务
{
    UINT32 index;
    UINT32 size;
    UINT32 ret;

    g_taskMaxNum = LOSCFG_BASE_CORE_TSK_LIMIT;
    size = (g_taskMaxNum + 1) * sizeof(LosTaskCB);
    /*
     * This memory is resident memory and is used to save the system resources
     * of task control block and will not be freed.
     */
    // g_taskCBArray = (LosTaskCB *)LOS_MemAlloc(m_aucSysMem0, size);
    g_taskCBArray = (LosTaskCB *)malloc(size);

    if (g_taskCBArray == NULL) {
        ret = LOS_ERRNO_TSK_NO_MEMORY;
        goto EXIT;
    }
    // (VOID)memset_s(g_taskCBArray, size, 0, size);
    (VOID)memset(g_taskCBArray, 0, size);

    LOS_ListInit(&g_losFreeTask);
    LOS_ListInit(&g_taskRecycleList);
    for (index = 0; index < g_taskMaxNum; index++) {
        g_taskCBArray[index].taskStatus = OS_TASK_STATUS_UNUSED;
        g_taskCBArray[index].taskID = index;
        g_taskCBArray[index].processCB = processCB;
        LOS_ListTailInsert(&g_losFreeTask, &g_taskCBArray[index].pendList);
    }

    g_taskCBArray[index].taskStatus = OS_TASK_STATUS_UNUSED;
    g_taskCBArray[index].taskID = index;
    g_taskCBArray[index].processCB = processCB;

    ret = OsSchedInit();

EXIT:
    if (ret != LOS_OK) {
        // PRINT_ERR("OsTaskInit error\n");
    }
    return ret;
}

STATIC UINT32 TaskCreateParamCheck(const UINT32 *taskID, TSK_INIT_PARAM_S *initParam)
{
    // UINT32 poolSize = OS_SYS_MEM_SIZE;

    if (taskID == NULL) {
        return LOS_ERRNO_TSK_ID_INVALID;
    }

    if (initParam == NULL) {
        return LOS_ERRNO_TSK_PTR_NULL;
    }

    // if (!OsProcessIsUserMode((LosProcessCB *)initParam->processID)) {
    //     if (initParam->pcName == NULL) {
    //         return LOS_ERRNO_TSK_NAME_EMPTY;
    //     }
    // }

    // if (initParam->pfnTaskEntry == NULL) {
    //     return LOS_ERRNO_TSK_ENTRY_NULL;
    // }

    // if (initParam->usTaskPrio > OS_TASK_PRIORITY_LOWEST) {
    //     return LOS_ERRNO_TSK_PRIOR_ERROR;
    // }

    // if (initParam->uwStackSize > poolSize) {
    //     return LOS_ERRNO_TSK_STKSZ_TOO_LARGE;
    // }

    // if (initParam->uwStackSize == 0) {
    //     initParam->uwStackSize = LOSCFG_BASE_CORE_TSK_DEFAULT_STACK_SIZE;
    // }
    // initParam->uwStackSize = (UINT32)ALIGN(initParam->uwStackSize, LOSCFG_STACK_POINT_ALIGN_SIZE);

    // if (initParam->uwStackSize < LOS_TASK_MIN_STACK_SIZE) {
    //     return LOS_ERRNO_TSK_STKSZ_TOO_SMALL;
    // }

    return LOS_OK;
}

STATIC UINT32 TaskCBInit(LosTaskCB *taskCB, const TSK_INIT_PARAM_S *initParam)
{
    UINT32 ret;
    UINT32 numCount;
    SchedParam schedParam = { 0 };
    LosSchedParam initSchedParam = {0};
    UINT16 policy = (initParam->policy == LOS_SCHED_NORMAL) ? LOS_SCHED_RR : initParam->policy;

    // TaskCBBaseInit(taskCB, initParam);

    schedParam.policy = policy;
    // ret = OsProcessAddNewTask(initParam->processID, taskCB, &schedParam, &numCount); // 将任务添加到进程
    // if (ret != LOS_OK) {
    //     return ret;
    // }

    if (policy == LOS_SCHED_DEADLINE) {
        initSchedParam.runTimeUs = initParam->runTimeUs;
        initSchedParam.deadlineUs = initParam->deadlineUs;
        initSchedParam.periodUs = initParam->periodUs;
    } else {
        initSchedParam.priority = initParam->usTaskPrio;
    }
    ret = OsSchedParamInit(taskCB, policy, &schedParam, &initSchedParam);
    if (ret != LOS_OK) {
        return ret;
    }

    // if (initParam->pcName != NULL) {
    //     ret = (UINT32)OsSetTaskName(taskCB, initParam->pcName, FALSE);
    //     if (ret == LOS_OK) {
    //         return LOS_OK;
    //     }
    // }

    // if (snprintf_s(taskCB->taskName, OS_TCB_NAME_LEN, OS_TCB_NAME_LEN - 1, "thread%u", numCount) < 0) {
    //     return LOS_NOK;
    // }
    return LOS_OK;
}

STATIC LosTaskCB *GetFreeTaskCB(VOID)
{
    UINT32 intSave;

    // SCHEDULER_LOCK(intSave);
    if (LOS_ListEmpty(&g_losFreeTask)) {
        // SCHEDULER_UNLOCK(intSave);
        // PRINT_ERR("No idle TCB in the system!\n");
        return NULL;
    }

    LosTaskCB *taskCB = OS_TCB_FROM_PENDLIST(LOS_DL_LIST_FIRST(&g_losFreeTask));
    LOS_ListDelete(LOS_DL_LIST_FIRST(&g_losFreeTask));
    // SCHEDULER_UNLOCK(intSave);

    return taskCB;
}

LITE_OS_SEC_TEXT_INIT UINT32 LOS_TaskCreateOnly(UINT32 *taskID, TSK_INIT_PARAM_S *initParam)
{
    UINT32 errRet = TaskCreateParamCheck(taskID, initParam);
    if (errRet != LOS_OK) {
        return errRet;
    }

#ifdef errRet
    __CPROVER_assert(errRet == LOS_OK, "VR13: 创建任务时，任务初始化参数检查无误");
#endif
    LosTaskCB *taskCB = GetFreeTaskCB();
    if (taskCB == NULL) {
        return LOS_ERRNO_TSK_TCB_UNAVAILABLE;
    }

    errRet = TaskCBInit(taskCB, initParam);
    if (errRet != LOS_OK) {
        goto DEINIT_TCB;
    }

    // errRet = TaskSyncCreate(taskCB);
    // if (errRet != LOS_OK) {
    //     goto DEINIT_TCB;
    // }

    // errRet = TaskStackInit(taskCB, initParam);
    // if (errRet != LOS_OK) {
    //     goto DEINIT_TCB;
    // }

    // if (OsConsoleIDSetHook != NULL) {
    //     OsConsoleIDSetHook(taskCB->taskID, OsCurrTaskGet()->taskID);
    // }

    *taskID = taskCB->taskID;
    // OsHookCall(LOS_HOOK_TYPE_TASK_CREATE, taskCB);
    return LOS_OK;

DEINIT_TCB:
    // TaskCBDeInit(taskCB);
#ifdef USECBMC
    __CPROVER_assume(0); 
#endif
    return errRet;
}

LITE_OS_SEC_TEXT_INIT UINT32 LOS_TaskCreate(UINT32 *taskID, TSK_INIT_PARAM_S *initParam)
{
    UINT32 ret;
    // UINT32 intSave;

    if (initParam == NULL) {
        return LOS_ERRNO_TSK_PTR_NULL;
    }

#ifdef USECBMC
    __CPROVER_assert(initParam != 0, "VR5: 创建任务时，任务初始化参数不为空");
#endif

    /* cbmc非确定性建模，模拟是否处于中断状态 */
    UINT32 Os_Int_Active;
#ifdef USECBMC
    Os_Int_Active = nondet_uint32();
    __CPROVER_assume(Os_Int_Active == 0 || Os_Int_Active == 1);
#else
    Os_Int_Active = 0;
#endif


    if (Os_Int_Active) {
        return LOS_ERRNO_TSK_YIELD_IN_INT;
    }

#ifdef USECBMC
    __CPROVER_assert(Os_Int_Active == 0, "VR1: 创建任务时，不处于中断状态");
#endif

    // 不考虑进程
    // if (OsProcessIsUserMode(OsCurrProcessGet())) {
    //     initParam->processID = (UINTPTR)OsGetKernelInitProcess();
    // } else {
    //     initParam->processID = (UINTPTR)OsCurrProcessGet();
    // }

    ret = LOS_TaskCreateOnly(taskID, initParam);
    if (ret != LOS_OK) {
        return ret;
    }

    LosTaskCB *taskCB = OS_TCB_FROM_TID(*taskID);

#ifdef USECBMC
    __CPROVER_assert(taskCB != NULL, "VR2: 创建任务后，任务控制块不为空");
    __CPROVER_assert(taskCB->ops != NULL, "VR3: 创建任务后，任务控制块的操作函数不为空");
    __CPROVER_assert(taskCB->ops->enqueue != NULL, "VR4: 创建任务后，任务控制块的入队函数不为空");
#endif
    // SCHEDULER_LOCK(intSave);
    taskCB->ops->enqueue(OsSchedRunqueue(), taskCB);
    // SCHEDULER_UNLOCK(intSave);

    /* in case created task not running on this core,
       schedule or not depends on other schedulers status. */
    // LOS_MpSchedule(OS_MP_CPU_ALL);

    // 只考虑创建任务，调度手动触发
    // if (OS_SCHEDULER_ACTIVE) {
    //     LOS_Schedule();
    // }

    return LOS_OK;
}