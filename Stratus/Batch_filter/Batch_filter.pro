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

SOURCES += \ 
		Batch_filter.cpp \ 
		main.cpp \ 
		system.cpp \ 
		tb.cpp \ 

HEADERS += \ 
		Batch_filter.h \ 
		Batch_filter_input_type.h \ 
		Batch_filter_output_type.h \ 
		system.h \ 
		tb.h \ 
    FloatType.h \
    Coefficients.h \
    Buffer_Types.h

OTHER_FILES += \ 
		Makefile \ 
		project.tcl \ 

