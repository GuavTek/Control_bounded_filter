#!/usr/local/bin/python3.9

import os
import sys
import numpy as np
import plot

# Arguments to pass directly to simulation script
superarg = ''
# Output file prefix
outfileName = 'results_batch_exp'
topModule = 'Batch'
topExp = 8
for arg in sys.argv:
    content = arg.split('=')
    if content[0] == 'help':
        os.system('./simulate.py -help')
        sys.exit()
    elif content[0] == '-exp':
        topExp = int(content[1])
    elif content[0] == '-out':
        outfileName = content[1]
    elif content[0] == '-top':
        if content[1] == 'TB_BATCH':
            topModule = 'Batch'
        elif content[1] == 'TB_FIR':
            topModule = 'FIR'
        elif content[1] == 'TB_FIR_Fixed':
            topModule = 'FIR fixedpoint'
        elif content[1] == 'TB_BATCH_Fixed':
            topModule = 'Batch Fixedpoint'
        superarg = superarg + ' ' + arg
    else:
        superarg = superarg + ' ' + arg
print(superarg)
for i in range(1, topExp+1):
    os.system('./simulate.sh' + superarg + ' -out=' + outfileName + str(i) + ' -exp=' + str(i))
plot.PlotSeries(outfileName, np.arange(1, topExp+1), topModule + ' with exponent bits = ', 12, 240e6, topModule + " SNR", "Exponent bits")

