use_hls_lib "memlib1"
#
# BDW Project File
#

############################################################
# Project Parameters
############################################################
#
# Technology Libraries
#
#techLib		"/eda/kits/stm/28nm_fdsoi_v12/C28SOI_SC_12_CORE_LL/5.1-06.82/libs/C28SOI_SC_12_CORE_LL_ss28_0.80V_0.00V_0.00V_0.00V_125C.lib.gz"
techLib         "/eda/kits/stm/28nm_fdsoi_v12/C28SOI_SC_12_CORE_LR/5.1-05.81/libs/C28SOI_SC_12_CORE_LR_ff28_0.80V_125C.lib"
techLib         "/eda/kits/stm/28nm_fdsoi_v12/C28SOI_SC_12_CLK_LR/5.1-06.81/libs/C28SOI_SC_12_CLK_LR_ff28_0.80V_125C.lib"
techLib         "/eda/kits/stm/28nm_fdsoi_v12/C28SOI_SC_12_PR_LR/5.3.a-00.80/libs/C28SOI_SC_12_PR_LR_ff28_0.80V_125C.lib"

#
# Include floating point library
#

use_hls_lib cynw_cm_float

#
# Global cynthHL command line options
#
# 504MHz -> 1.984ns
# 252MHz -> 3.968ns
cynthHLOptions "--clock_period=4 \
                --message_detail=2 \
                "

# Delay target?
ccOptions "-DCLOCK_PERIOD=4 -g"

#
# Simulation Options
#
use_verilog_simulator mti
logOptions      vcd
endOfSimCommand "make saySimPassed"

#
# Testbench or System Level Modules
#
systemModule main.cpp
systemModule system.cpp
systemModule tb.cpp

set_attr timing_aggression 0

#
# SC_MODULES to be Cynthesized
#
array unset cynCfg
array set cynCfg {
        BASIC		{--power=on --inline_partial_constants=on}
        DPA			{--power=on --inline_partial_constants=on --dpopt_auto=op,expr}
}
#
#	The following rules are TCL code to create the cynthConfig
#	entries and simulation configuration entries for each Cynthesizer
#	configuration entries.
#
set cfg {}
foreach cc [lsort -dict [array names cynCfg]] { append cfg "$cc $cynCfg($cc) " }
cynthModule Batch_filter Batch_filter.cpp [cynthConfigs $cfg] [vlogFiles {}]
foreach cc [lsort -dict [array names cynCfg]] {
  simConfig ${cc}_C [subst {Batch_filter RTL_C $cc}]
  simConfig ${cc}_V [subst {Batch_filter RTL_V $cc}]
  simConfig ${cc}_CA [subst {Batch_filter CA $cc}]
  define_power_config ${cc}_P ${cc}_V
}

simConfig B 		{Batch_filter}


