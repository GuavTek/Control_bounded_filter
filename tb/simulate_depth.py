#!/usr/local/bin/python3.9

import os
import sys
import numpy as np
import plot

# Arguments to pass directly to simulation script
superarg = ''
# Output file prefix
outfileName = 'batch_fx'
topModule = 'Batch Fixed'
dsr = 12
topDepth = 100
for arg in sys.argv:
    content = arg.split('=')
    if content[0] == '-help':
        print("Simulation depth script overrides following property:")
        print("-depth=\t\t the highest filter depth in the sweep\n")
        os.system('./simulate.py -help')
        sys.exit()
    elif content[0] == '-depth':
        topDepth = int(content[1])
    elif content[0] == '-out':
        outfileName = content[1]
    elif content[0] == '-dsr':
        dsr = int(content[1])
        superarg += ' ' + arg
    elif content[0] == '-top':
        if content[1] == 'TB_BATCH':
            topModule = 'Batch'
        elif content[1] == 'TB_FIR':
            topModule = 'FIR'
        elif content[1] == 'TB_FIR_Fixed':
            topModule = 'FIR Fixedpoint'
        elif content[1] == 'TB_BATCH_Fixed':
            topModule = 'Batch Fixedpoint'
        elif content[1] == 'TB_HYBRID_Fixed':
            topModule = 'Hybrid Fixedpoint'
        superarg = superarg + ' ' + arg
    elif content[0].find('.py') != -1:
        # Skip self-reference
        continue
    else:
        superarg += ' ' + arg
print(superarg)

for i in range(40, topDepth+1, 4):
    os.system('./simulate.py -noplot' + superarg + ' -out=' + outfileName + str(i) + ' -depth=' + str(i))

# Plots the sweep with dsr= 2 and 12
plot.PlotSeries([outfileName + '_dsr2_c', outfileName + '_dsr12_c'], np.arange(40, topDepth+1, 4), topModule + f' Filter depth = ', [2, 12], 240e6, topModule + " - SNR vs Depth", "Depth")

