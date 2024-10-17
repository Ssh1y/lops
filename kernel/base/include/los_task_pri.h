#ifndef _LOS_TASK_PRI_H
#define _LOS_TASK_PRI_H

#include "los_task.h"
#include "los_sched_pri.h"

#ifdef __cplusplus
#if __cplusplus
extern "C" {
#endif /* __cplusplus */
#endif /* __cplusplus */

/**
 * @ingroup los_task
 * Define task signal types.
 *
 * Task signal types.
 */
#define SIGNAL_NONE                 0U
#define SIGNAL_KILL                 (1U << 0)
#define SIGNAL_SUSPEND              (1U << 1)
#define SIGNAL_AFFI                 (1U << 2)

/* scheduler lock */
// extern SPIN_LOCK_S g_taskSpin;
#define SCHEDULER_HELD()            LOS_SpinHeld(&g_taskSpin)
#define SCHEDULER_LOCK(state)       LOS_SpinLockSave(&g_taskSpin, &(state))
#define SCHEDULER_UNLOCK(state)     LOS_SpinUnlockRestore(&g_taskSpin, state)

/* default and non-running task's ownership id */
#define OS_TASK_INVALID_CPUID       0xFFFF

/**
 * @ingroup los_task
 * Null task ID
 *
 */
#define OS_TASK_ERRORID             0xFFFFFFFF

/**
 * @ingroup los_task
 * Flag that indicates the task or task control block status.
 *
 * The task control block is unused.
 */
#define OS_TASK_STATUS_UNUSED       0x0400U

/**
 * @ingroup los_task
 * Flag that indicates the task or task control block status.
 *
 * The task is joinable.
 */
#define OS_TASK_FLAG_PTHREAD_JOIN   0x0800U

/**
 * @ingroup los_task
 * Flag that indicates the task or task control block status.
 *
 * The task is user mode task.
 */
#define OS_TASK_FLAG_USER_MODE      0x1000U

/**
 * @ingroup los_task
 * Flag that indicates the task property.
 *
 * The task is system-level task, like idle, swtmr and etc.
 */
#define OS_TASK_FLAG_SYSTEM_TASK    0x2000U

/**
 * @ingroup los_task
 * Flag that indicates the task property.
 *
 * The task is no-delete system task, like resourceTask.
 */
#define OS_TASK_FLAG_NO_DELETE      0x4000U

/**
 * @ingroup los_task
 * Flag that indicates the task property.
 *
 * Kills the thread during process exit.
 */
#define OS_TASK_FLAG_EXIT_KILL       0x8000U

/**
 * @ingroup los_task
 * Flag that indicates the task property.
 *
 * Specifies the process creation task.
 */
#define OS_TASK_FLAG_SPECIFIES_PROCESS 0x0U

/**
 * @ingroup los_task
 * Boundary on which the stack size is aligned.
 *
 */
#define OS_TASK_STACK_SIZE_ALIGN    16U

/**
 * @ingroup los_task
 * Boundary on which the stack address is aligned.
 *
 */
#define OS_TASK_STACK_ADDR_ALIGN    8U

/**
 * @ingroup los_task
 * Number of usable task priorities.
 */
#define OS_TSK_PRINUM               (OS_TASK_PRIORITY_LOWEST - OS_TASK_PRIORITY_HIGHEST + 1)

/**
* @ingroup  los_task
* @brief Check whether a task ID is valid.
*
* @par Description:
* This API is used to check whether a task ID, excluding the idle task ID, is valid.
* @attention None.
*
* @param  taskID [IN] Task ID.
*
* @retval 0 or 1. One indicates that the task ID is invalid, whereas zero indicates that the task ID is valid.
* @par Dependency:
* <ul><li>los_task_pri.h: the header file that contains the API declaration.</li></ul>
* @see
*/
#define OS_TSK_GET_INDEX(taskID) (taskID)

/**
* @ingroup  los_task
* @brief Obtain the pointer to a task control block.
*
* @par Description:
* This API is used to obtain the pointer to a task control block using a corresponding parameter.
* @attention None.
*
* @param  ptr [IN] Parameter used for obtaining the task control block.
*
* @retval Pointer to the task control block.
* @par Dependency:
* <ul><li>los_task_pri.h: the header file that contains the API declaration.</li></ul>
* @see
*/
#define OS_TCB_FROM_PENDLIST(ptr) LOS_DL_LIST_ENTRY(ptr, LosTaskCB, pendList)

/**
* @ingroup  los_task
* @brief Obtain the pointer to a task control block.
*
* @par Description:
* This API is used to obtain the pointer to a task control block that has a specified task ID.
* @attention None.
*
* @param  TaskID [IN] Task ID.
*
* @retval Pointer to the task control block.
* @par Dependency:
* <ul><li>los_task_pri.h: the header file that contains the API declaration.</li></ul>
* @see
*/
#define OS_TCB_FROM_RTID(taskID) (((LosTaskCB *)g_taskCBArray) + (taskID))
#ifdef LOSCFG_PID_CONTAINER
#define OS_TCB_FROM_TID(taskID) OsGetTCBFromVtid(taskID)
#else
#define OS_TCB_FROM_TID(taskID) OS_TCB_FROM_RTID(taskID)
#endif

#ifndef LOSCFG_STACK_POINT_ALIGN_SIZE
#define LOSCFG_STACK_POINT_ALIGN_SIZE                       (sizeof(UINTPTR) * 2)
#endif

#define OS_TASK_RESOURCE_STATIC_SIZE    0x1000
#define OS_TASK_RESOURCE_FREE_PRIORITY  5
#define OS_RESOURCE_EVENT_MASK          0xFF
#define OS_RESOURCE_EVENT_OOM           0x02
#define OS_RESOURCE_EVENT_FREE          0x04

/**
 * @ingroup los_task
 * Maximum number of tasks.
 *
 */
extern UINT32 g_taskMaxNum;

/**
 * @ingroup los_task
 * Starting address of a task.
 *
 */
extern LosTaskCB *g_taskCBArray;


extern UINT32 OsTaskInit(UINTPTR processCB);

#ifdef __cplusplus
#if __cplusplus
}
#endif /* __cplusplus */
#endif /* __cplusplus */

#endif /* _LOS_TASK_PRI_H */