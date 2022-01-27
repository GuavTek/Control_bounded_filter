#!/usr/local/bin/python3.9
import plot
import sys

try:
    res = plot.ReadResultFile('results/' + sys.argv[1], 13) 
except:
    print("First argument must be filename")

try:
    label = sys.argv[2]
except:
    print("Second argument must be label")
length = res.size
DSR = 12
plot.PlotFigure(res, int(960/DSR), label, sys.argv[1], 240e6/DSR)