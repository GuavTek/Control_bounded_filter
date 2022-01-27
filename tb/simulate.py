#!/usr/local/bin/python3.9

import os
import sys
import plot
import math

#os.system("rm -rf work*")

# Arguments to pass directly to xcelium script
superarg = ''
# Output file prefix
outfileName = 'results_batch_mant'
topModule = 'TB_BATCH'
mant = 23
exp = 8
OSR = 1
depth = 100
plotResults = 1
for arg in sys.argv:
    content = arg.split('=')
    if content[0] == '-help':
        print("Simulation script halp:")
        print("-out=\t\t Name of csv file with results")
        print("-mant=\t\t Number of mantissa bits used in design")
        print("-exp=\t\t Number of exponent bits (floating point) or integer bits (fixed point)")
        print("-osr=\t\t Downsampling rate")
        print("-depth\t\t Define the size of filter/batches")
        print("-top=\t\t Name of testbench module")
        print("-verbose=\t Change how many checks are performed")
        print("-noplot\t\t Skip plotting of results")
        sys.exit()
    elif content[0] == '-out':
        outfileName = content[1]
        superarg += ' -define OUT_FILE=' + content[1]
    elif content[0] == '-mant':
        mant = int(content[1])
        superarg += ' -define MANT_W=' + content[1]
    elif content[0] == '-exp':
        exp = int(content[1])
        superarg += ' -define EXP_W=' + content[1]
    elif content[0] == '-noplot':
        plotResults = 0
    elif content[0] == '-verbose':
        superarg += ' -define VERBOSE_LVL=' + content[1]
    elif content[0] == '-depth':
        depth = int(content[1])
        superarg += ' -define DEPTH=' + content[1]
    elif content[0] == '-osr':
        OSR = int(content[1])
        superarg += ' -define OSR=' + content[1]
    elif content[0] == '-osr1':
        OSR *= int(content[1])
        superarg += ' -define OSR1=' + content[1]
    elif content[0] == '-osr2':
        OSR *= int(content[1])
        superarg += ' -define OSR2=' + content[1]
    elif content[0] == '-top':
        topModule = content[1]
    elif content[0].find('.py') != -1:
        continue
    else:
        superarg += ' ' + arg

if topModule == 'TB_BATCH':
    topName = 'Batch'
elif topModule == 'TB_FIR':
    topName = 'FIR'
elif topModule == 'TB_FIR_Fixed':
    topName = 'FIR Fixedpoint'
elif topModule == 'TB_BATCH_Fixed':
    topName = 'Batch Fixedpoint'
elif topModule == 'TB_CUMUL_Fixed':
    topName = 'Cumulative'
elif topModule == 'TB_HYBRID_Fixed':
    topName = 'Hybrid Fixedpoint'

superarg += ' -top work.' + topModule + ' ' + topModule + '.sv'
print(superarg)

if os.system('xrun -faccess +r -SV -incdir ../sv/ -incdir ../sv/HardFloat-1/source/ ' + superarg):
    print("Failure... :(")
    #sys.exit(1)
else:
    print("Success! :)")

if plotResults:
    res = plot.ReadResultFile('results/' + outfileName, 13)
    if topModule.find('BATCH') != -1:
        label = topName + f" with format {exp}p{mant}, {depth} batch size, and OSR={OSR}"
    elif topModule.find('FIR') != -1:
        label = topName + f" with format {exp}p{mant}, {depth} coefficients, and OSR={OSR}"
    elif topModule.find('CUMUL') != -1:
        label = topName + f" with format {exp}p{mant}, {depth} lookahead length, and OSR={OSR}"
    elif topModule.find('HYBRID') != -1:
        label = topName + f" with format {exp}p{mant}, {depth} lookahead length, and OSR={OSR}"
    plot.PlotFigure(res[int(math.ceil(1920/OSR)):int(-1920/OSR)], int(960/OSR), label, outfileName, 240e6/OSR)

