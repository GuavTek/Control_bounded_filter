#!/usr/local/bin/python3.9

import os
import sys
import plot
import math

# Arguments to pass directly to xcelium script
superarg = ''

# Output file prefix
outfileName = 'results_batch_mant'
topModule = 'TB_BATCH'
mant = 23
exp = 8
DSR = 1
depth = 100
plotResults = 1
for arg in sys.argv:
    content = arg.split('=')
    if content[0] == '-help':
        print("Simulation script halp:")
        print("-out=\t\t Name of csv file with results")
        print("-mant=\t\t Number of mantissa bits used in design")
        print("-exp=\t\t Number of exponent bits (floating point) or integer bits (fixed point)")
        print("-dsr=\t\t Downsampling rate")
        print("-depth\t\t Define the size of filter/batches")
        print("-top=\t\t Name of testbench module")
        print("-verbose=\t Change how much info is printed to screen")
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
    elif content[0] == '-dsr':
        DSR = int(content[1])
        superarg += ' -define DSR=' + content[1]
    elif content[0] == '-dsr1':
        DSR *= int(content[1])
        superarg += ' -define DSR1=' + content[1]
    elif content[0] == '-dsr2':
        DSR *= int(content[1])
        superarg += ' -define DSR2=' + content[1]
    elif content[0] == '-top':
        topModule = content[1]
    elif content[0].find('.py') != -1:
        # Skip self-reference
        continue
    else:
        # Pass unknown arguments to excelium
        superarg += ' ' + arg

superarg += ' -top work.' + topModule + ' ' + topModule + '.sv'
print(superarg)

if os.system('xrun -faccess +r -SV -incdir ../sv/ -incdir ../sv/HardFloat-1/source/ ' + superarg):
    print("Failure... :(")
    #sys.exit(1)
else:
    print("Success! :)")

if plotResults:
    # Set name for label
    if topModule == 'TB_Batch_Flp':
        topName = 'Batch Floating-point'
    elif topModule == 'TB_FIR_Flp':
        topName = 'FIR Floating-point'
    elif topModule == 'TB_FIR_Fxp':
        topName = 'FIR Fixed-point'
    elif topModule == 'TB_Batch_Fxp':
        topName = 'Batch Fixed-point'
    elif topModule == 'TB_Cumulative_Fxp':
        topName = 'Cumulative'
    elif topModule == 'TB_Hybrid_Fxp':
        topName = 'Hybrid Fixed-point'
    elif topModule == 'TB_Hybrid_Twostage_Fxp':
        topName = 'Hybrid two-stage'
    elif topModule == 'TB_Batch_Twostage_Fxp':
        topName = 'Batch two-stage'
    # Read results
    res = plot.ReadResultFile('results/' + outfileName, 13)
    if topModule.find('Batch') != -1:
        label = topName + f" with format {exp}p{mant}, {depth} batch size, and DSR={DSR}"
    elif topModule.find('FIR') != -1:
        label = topName + f" with format {exp}p{mant}, {depth} coefficients, and DSR={DSR}"
    elif topModule.find('TB_Cumulative') != -1:
        label = topName + f" with format {exp}p{mant}, {depth} lookahead length, and DSR={DSR}"
    elif topModule.find('Hybrid') != -1:
        label = topName + f" with format {exp}p{mant}, {depth} lookahead length, and DSR={DSR}"
    plot.PlotFigure(res[int(math.ceil(1920/DSR)):int(-1920/DSR)], int(960/DSR), label, outfileName, 240e6/DSR)

