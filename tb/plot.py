#!/usr/local/bin/python3.9
import numpy as np
from matplotlib import pyplot as plt
import csv

def PlotSNR(ticks, SNRs, tit, paramX, fileName, legend=[]):
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
    plt.rc('font', **{'family' : 'DejaVu Sans', 'weight' : 'normal', 'size' : 12})
    for wav in SNRs:
        plt.plot(ticks, wav)
    if len(legend) > 0:
        plt.legend(legend)
    plt.title(tit, fontsize=16)
    plt.ylabel("SNR [dB]")
    plt.xlabel(paramX)
    plt.minorticks_off()
    plt.xticks(ticks, xdisp, rotation=45)
    #plt.figtext(0.13, 0.85, "Peak is " + ('%.2f' % peak) + "dB with " + paramX + " = " + str(int(ticks[where])))
    plt.grid(True)
    plt.savefig("plots/" + fileName)

# Plot a section of the wave
def PlotWave(arr, length):
	k = np.arange(0, length)
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

	arr_f[0] = 0
	arr_f[1] = 0

	#Calculate noise power
	Pn = sum(arr_f)

	SNR = 10*np.log10(Ps/Pn)
	return SNR

# Makes a figure of wave arr, and returns SNR
def PlotFigure(arr, plotLength, label, fileName, fs):
	plt.figure(figsize=(10, 8))
	plt.rc('font', **{'family' : 'DejaVu Sans', 'weight' : 'normal', 'size' : 12})
	plt.subplot(2,1,1)
	plt.title(label, fontsize=16)
	PlotWave(arr, plotLength)

	plt.subplot(2,1,2)
	SNR = PlotPSD(arr, fs, 1)
	plt.figtext(0.13, 0.42, "SNR = " + ('%.2f' % SNR) + "dB")
	plt.savefig("plots/" + fileName)
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


def PlotSeries(prefix, suffixes, label, dsr, fs, tit, paramX):
	allSNR = []
	legend = []
	if type(prefix) != list:
		prefix = [prefix]
	if type(dsr) != list:
		dsr = [dsr]
	i = 0
	for s in prefix:
		SNRs = []
		o = dsr[i]
		legend.append('DSR=' + str(o))
		ffff = open('results/' + s + '_SNR.csv', 'w', newline='')
		w = csv.writer(ffff, delimiter=',')
		for num in suffixes:
			results = ReadResultFile("results/" + s + str(num), 13)
			tempSNR = PlotFigure(results[int(1920/o):-int(1920/o)], int(960/o), label + str(num), s + str(num), fs/o)
			SNRs.append(tempSNR)
			w.writerow([num, tempSNR])
		ffff.close()
		allSNR.append(SNRs)
		i += 1
	PlotSNR(suffixes, allSNR, tit, paramX, prefix[0] + "_SNR", legend)
	
