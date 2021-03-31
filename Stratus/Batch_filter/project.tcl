#
# BDW Project File
#

############################################################
# Project Parameters
############################################################
#
# Technology Libraries
#
techLib		"/eda/kits/stm/28nm_fdsoi_v12/C28SOI_SC_12_CORE_LL/5.1-06.82/libs/C28SOI_SC_12_CORE_LL_ss28_1.00V_0.00V_0.00V_0.00V_125C.lib.gz"

#
# Include floating point library
#

use_hls_lib cynw_cm_float

#
# Global cynthHL command line options
#
cynthHLOptions "--clock_period=1.984 \
                --message_detail=2 \
                "

ccOptions "-DCLOCK_PERIOD=1.984 -g"

#
# Simulation Options
#
#verilogSimulator mti
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
	BASIC		{}
	DPA			{--dpopt_auto=op,expr}
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
}

simConfig B 		{Batch_filter}




