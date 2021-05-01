#################################################
# Stratus IDE project file generated;
#################################################
QT       += core

QT       -= gui

CONFIG   += console
CONFIG   -= app_bundle

STRATUSHOME = $$(STRATUS_HOME)
SYSTEMCHOME = $$(SYSTEMC)

TEMPLATE = app
INCLUDEPATH += $${SYSTEMCHOME}/include
INCLUDEPATH += $${SYSTEMCHOME}/include/tlm
INCLUDEPATH += $${STRATUSHOME}/share/stratus/include
INCLUDEPATH += ./bdw_work/wrappers
INCLUDEPATH += ./
INCLUDEPATH += memlib1/c_parts

SOURCES += \ 
		Batch_filter.cpp \ 
		main.cpp \ 
		system.cpp \ 
		tb.cpp \ 
		memlib1/c_parts/DualRAM.cc \ 

HEADERS += \ 
		Batch_filter.h \ 
		Batch_filter_input_type.h \ 
		Batch_filter_output_type.h \ 
		Buffer_Types.h \ 
		Coefficients.h \ 
		FloatType.h \ 
		system.h \ 
		tb.h \ 
		memlib1/c_parts/DualRAM.h \ 

OTHER_FILES += \ 
		Makefile \ 
		project.tcl \ 

