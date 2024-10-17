/**
 * @defgroup los_hw Hardware
 * @ingroup kernel
 */

#ifndef _LOS_HW_CPU_H
#define _LOS_HW_CPU_H

#include "los_typedef.h"

// STATIC INLINE VOID *ArchCurrTaskGet(VOID)
// {
    // return (VOID *)(UINTPTR)ARM_SYSREG_READ(TPIDRPRW);
//     return g_runTask;
// }

// STATIC INLINE VOID ArchCurrTaskSet(VOID *val)
// {
    // ARM_SYSREG_WRITE(TPIDRPRW, (UINT32)(UINTPTR)val);
//     g_runTask = (LosTaskCB *)val;
// }

STATIC UINT32 ArchCurrCpuid(VOID)
{
#ifdef LOSCFG_KERNEL_SMP
    return ARM_SYSREG_READ(MPIDR) & MPIDR_CPUID_MASK;
#else
    return 0;
#endif
}

#endif /* _LOS_HW_CPU_H */