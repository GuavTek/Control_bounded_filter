###########################################################################
#
#  Copyright (C) 2008-2010, Forte Design Systems. All Rights Reserved.
#
###########################################################################
#
# Makefile - top-level project makefile
#
######################################################################
# list subdirectories that contain memory libraries
# (must be in subdirectories of the current directory)
MEMLIBS =

# list subdirectories that contain interface libraries
# (must be in subdirectories of the current directory)
IFLIBS =

# Uncomment this line to use the Insight debugger
#BDW_DEBUG = 1

BASE_PATH = ~/projects/spring2021/28nm/digital_flow/ex/Stratus/Batch_filter

saySimPassed:
	@bdw_sim_pass

-include Makefile.prj

Makefile.prj : project.tcl
	@bdw_makegen

xcelium: $(BDW_VLOGSIM_DEPS) \
    $(BDW_SIM_ENV_SETUP) xcelium $(BDW_VLOG_DUT_FILES) \
    $(BDW_VLOGCOMP_ARGS) \
    libext.v $(BDW_VLOG_LIBS) \
    $(BDW_VLOGSIM_ARGS) \
    -l $(BASE_PATH)/$(BDW_SIM_CONFIG_DIR)/sim.log \
    $(BDW_END_OF_SIM_CMD)

# Clean out undesirable junk files from the project directory
# Uses the automatically created clean_all target from Makefile.prj
clean: clean_all clean_libs
	@rm -f transcript vsim* *.wlf data.out
	@rm -f *~ *.bak *.BAK
	@rm -rf work debussy* vfast*
	@rm -f Makefile.prj
	@rm -f msg_help.html
	@rm -rf core
	@rm -rf core.*
	@rm -rf .stack.*

CLEAN: clean

