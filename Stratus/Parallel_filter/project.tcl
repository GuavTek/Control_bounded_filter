#
# BDW Project File
#

############################################################
# Project Parameters
############################################################
#
# Technology Libraries
#

#set TSpeed "ss"
#set TThreshold "LL"
#set TVersion "5.1-06.82"
#set TTemp "125C"
#set TVoltage "1.00"

#techLib		"/eda/kits/stm/28nm_fdsoi_v12/C28SOI_SC_12_CORE_LL/5.1-06.82/libs/C28SOI_SC_12_CORE_LL_ss28_1.00V_0.00V_0.00V_0.00V_125C.lib.gz"
techLib         "/eda/kits/stm/28nm_fdsoi_v12/C28SOI_SC_12_CORE_LR/5.1-05.81/libs/C28SOI_SC_12_CORE_LR_ss28_0.80V_m25C.lib"
techLib         "/eda/kits/stm/28nm_fdsoi_v12/C28SOI_SC_12_CLK_LR/5.1-06.81/libs/C28SOI_SC_12_CLK_LR_ss28_0.80V_m25C.lib"
techLib         "/eda/kits/stm/28nm_fdsoi_v12/C28SOI_SC_12_PR_LR/5.3.a-00.80/libs/C28SOI_SC_12_PR_LR_ss28_0.80V_m25C.lib"

#
# Global cynthHL command line options
#
cynthHLOptions "--clock_period=4 --message_detail=2 \
             "

ccOptions "-DCLOCK_PERIOD=4 -g"

#
# Include floating point library
#

use_hls_lib cynw_cm_float

#
# Simulation Options
#
verilogSimulator mti
logOptions      vcd
endOfSimCommand "make saySimPassed"

#
# Testbench or System Level Modules
#
systemModule main.cpp
systemModule system.cpp
systemModule tb.cpp

#
# SC_MODULES to be Cynthesized
#
array unset cynCfg
array set cynCfg {
        BASIC		{--inline_partial_constants=on}
        DPA			{--inline_partial_constants=on --balance_expr=delay --dpopt_auto=op,expr}
}
#
#	The following rules are TCL code to create the cynthConfig
#	entries and simulation configuration entries for each Cynthesizer 
#	configuration entries.
#
set cfg {}
foreach cc [lsort -dict [array names cynCfg]] { append cfg "$cc $cynCfg($cc) " }
cynthModule Parallel_filter Parallel_filter.cpp [cynthConfigs $cfg] [vlogFiles {}]
foreach cc [lsort -dict [array names cynCfg]] {
  simConfig ${cc}_C [subst {Parallel_filter RTL_C $cc}]
  simConfig ${cc}_V [subst {Parallel_filter RTL_V $cc}]
  simConfig ${cc}_CA [subst {Parallel_filter CA $cc}]
  define_power_config ${cc}_P ${cc}_V
}

simConfig B 		{Parallel_filter}




