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
dsr=12
for arg in sys.argv:
    content = arg.split('=')
    if content[0] == '-help':
        print("Simulation exponent script overrides following property:")
        print("-exp=\t\t the highest number of exponent bits in the sweep\n")
        os.system('./simulate.py -help')
        sys.exit()
    elif content[0] == '-exp':
        topExp = int(content[1])
    elif content[0] == '-out':
        outfileName = content[1]
    elif content[0] == '-dsr':
        dsr = int(content[1])
        superarg += ' ' + arg
    elif content[0] == '-top':
        if content[1] == 'TB_Batch_Flp':
            topModule = 'Batch Floating-point'
        elif content[1] == 'TB_FIR_Flp':
            topModule = 'FIR Floating-point'
        elif content[1] == 'TB_FIR_Fxp':
            topModule = 'FIR Fixed-point'
        elif content[1] == 'TB_Batch_Fxp':
            topModule = 'Batch Fixed-point'
        elif content[1] == 'TB_Hybrid_Fxp':
            topModule = 'Hybrid Fixed-point'
        superarg = superarg + ' ' + arg
    elif content[0].find('.py') != -1:
        # Skip self-reference
        continue
    else:
        superarg += ' ' + arg
print(superarg)

for i in range(1, topExp+1):
    os.system('./simulate.py -noplot' + superarg + ' -out=' + outfileName + str(i) + ' -exp=' + str(i))

plot.PlotSeries(outfileName, np.arange(1, topExp+1), topModule + ' with exponent bits = ', 12, 240e6/dsr, topModule + " SNR", "Exponent bits")

