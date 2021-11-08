#!/usr/local/bin/python3.9
import numpy as np
from matplotlib import pyplot as plt
import csv

def PlotSNR(ticks, SNRs, tit, paramX, fileName):
    # Display every 4th tick
    xdisp = []
    for i in range(0, ticks.size):
        if (i % 4 == 0):
            xdisp.append(str(ticks[i]))
        else:
            xdisp.append("")
    # Plot figure
    #peak = np.amax(SNRs)
    #where = np.where(SNRs == peak)
    #if (np.size(where) > 1):
    #    where = where[0]
    plt.figure(figsize=(10,8))
    plt.plot(ticks, SNRs)
    plt.title(tit)
    plt.ylabel("SNR [dB]")
    plt.xlabel(paramX)
    plt.minorticks_off()
    plt.xticks(ticks, xdisp, rotation=45)
    #plt.figtext(0.13, 0.85, "Peak is " + ('%.2f' % peak) + "dB with " + paramX + " = " + str(int(ticks[where])))
    plt.grid(True)
    plt.savefig("Data/plots/" + fileName)

# Plot a section of the wave
def PlotWave(arr, length, tit):
	k = np.arange(0, length)
	plt.title(tit)
	plt.xlabel("time k")
	plt.ylabel("result u")
	plt.plot(k, arr[:length])

# Plot the PSD and return SNR
def PlotPSD(arr, freq, sig_leak=1):
	T = 1.0 / freq
	arrLength = arr.size
	print("Plotting array with length: " + str(arrLength))

	arr_f, freq = plt.psd(arr, NFFT=arrLength, Fs=freq)
	plt.xscale('log')
	plt.grid(True)

	#Find signal position
	sigpos = max(range(len(arr_f)), key=lambda i: abs(arr_f[i]))

	#Normalize
	#arr_f = arr_f/arr_f[sigpos]

	#Calculate signal power
	Ps = 0
	for i in range(sigpos-sig_leak, sigpos+sig_leak+1):
		Ps = Ps + arr_f[i]
		arr_f[i] = 0

	#Calculate noise power
	Pn = sum(arr_f)

	SNR = 10*np.log10(Ps/Pn)
	return SNR

# Makes a figure of wave arr, and returns SNR
def PlotFigure(arr, plotLength, label, fileName, fs):
	plt.figure(figsize=(10, 8))
	plt.subplot(2,1,1)
	PlotWave(arr, plotLength, label)

	plt.subplot(2,1,2)
	SNR = PlotPSD(arr, fs, 1)
	plt.figtext(0.13, 0.42, "SNR = " + ('%.2f' % SNR) + "dB")
	plt.savefig(("Data/plots/" + fileName))
	plt.close()
	return SNR

def ReadResultFile(fileName, exp):
	csvfile = open(fileName + '.csv', newline='')
	r = csv.reader(csvfile, delimiter=',')
	temp = []
	for line in r:
		for num in line:
			num = num.replace("[", "")
			num = num.replace("]", "")
			try:
				temp.append(float(num)/2**exp)
			except:
				print("!!! Ignored from result: " + num)
	#	while (len(temp) < self.S_Length):
	#		temp.append(0.0)
	temp = np.array(temp)
	print("Read " + str(temp.size) + " samples")
	csvfile.close()
	return temp


def PlotSeries(prefix, suffixes, label, osr, fs, tit, paramX):
    SNRs = []
    for num in suffixes:
        results = ReadResultFile("Data/" + prefix + str(num), 0)
        SNRs.append(PlotFigure(results[int(2880/osr):-int(2880/osr)], int(960/osr), label + str(num), prefix + str(num), fs))
    PlotSNR(suffixes, SNRs, tit, paramX, prefix + "_SNR")

#PlotSeries("results_batch_exp", np.arange(3, 9), 'Batch with exponent bits = ', 12, 240e6, "Batch SNR", "Exponent bits")
#PlotSeries("results_batch_mant", np.arange(7, 24), 'Batch with mantissa bits = ', 12, 240e6, "Batch SNR", "Mantissa bits")
#results = ReadResultFile("Data/results_batch1", 0)
#PlotFigure(results[int(2880):-int(2880)], int(960), 'Batch with OSR = 1, batch size = 600', 'batch_OSR1', 240e6)
#results = ReadResultFile("Data/results_batch12", 0)
#PlotFigure(results[int(2880/12):-int(2880/12)], int(960/12), 'Batch with OSR = 12, batch size = 636', 'batch_OSR12', 20e6)
#results = ReadResultFile("Data/results_fir", 0)
#PlotFigure(results[int(2880/12):-int(2880/12)], int(960/12), 'FIR with OSR = 12, length = 96', 'fir_OSR12', 20e6)
