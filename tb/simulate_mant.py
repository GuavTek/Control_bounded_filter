#!/usr/local/bin/python3.9

import os
import sys
import numpy as np
import plot

# Arguments to pass directly to simulation script
superarg = ''
# Output file prefix
outfileName = 'results_batch_mant'
topModule = 'Batch'
topMant = 23
for arg in sys.argv:
    content = arg.split('=')
    if content[0] == 'help':
        os.system('./simulate.py -help')
        sys.exit()
    elif content[0] == '-mant':
        topMant = int(content[1])
    elif content[0] == '-out':
        outfileName = content[1]
    elif content[0] == '-top':
        if content[1] == 'TB_BATCH':
            topModule = 'Batch'
        elif content[1] == 'TB_FIR':
            topModule = 'FIR'
        elif content[1] == 'TB_FIR_Fixed':
            topModule = 'FIR Fixedpoint'
        elif content[1] == 'TB_BATCH_Fixed':
            topModule = 'Batch Fixedpoint'
        superarg = superarg + ' ' + arg
    else:
        superarg = superarg + ' ' + arg
print(superarg)
for i in range(7, topMant+1):
    os.system('./simulate.py -noplot' + superarg + ' -out=' + outfileName + str(i) + ' -mant=' + str(i))
plot.PlotSeries(outfileName, np.arange(7, topMant+1), topModule + ' with mantissa bits = ', 12, 240e6, topModule + " SNR", "Mantissa bits")

