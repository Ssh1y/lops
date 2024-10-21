CBMC = cbmc
SRC = VerifyCase.c \
      ../../kernel/base/sched/los_sched.c \
      ../../kernel/base/sched/los_priority.c \
      ../../kernel/base/sched/los_deadline.c \
      ../../kernel/base/core/los_task.c \
      ../../kernel/base/sched/los_sortlink.c

INCLUDES = -I ../../kernel/base/include \
           -I ../../kernel/include \
           -I ../../kernel/common \
           -I ../../arch/arm/arm/include/

DEFINES = -DUSECBMC -D "OS_SYS_CLOCK = 100000"
UNWIND = --unwind 13
CBMC_FLAGS = --no-built-in-assertions

ifdef TRACE
  TRACE_FLAG = --trace
else
  TRACE_FLAG =
endif

.PHONY: verify
verify:
	$(CBMC) $(SRC) $(INCLUDES) $(DEFINES) $(CBMC_FLAGS) $(UNWIND) $(TRACE_FLAG)
