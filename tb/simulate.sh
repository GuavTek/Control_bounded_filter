rm -rf work*

RED='\033[0;31m'
NC='\033[0m'   

SUPERARG=''

# Parse arguments
if [ $# -gt 0 ]
then
	for arg in $@
	do
		case $arg in '-gui')
			SUPERARG="${SUPERARG} -gui";;
		-top=*)
			TOP_MODULE=${arg#-top=};;
		-mant=*)
			SUPERARG="${SUPERARG} -define MANT_W=${arg#-mant=}";;
		-exp=*)
			SUPERARG="${SUPERARG} -define EXP_W=${arg#-exp=}";;
		-verbose=*)
			SUPERARG="${SUPERARG} -define VERBOSE_LVL=${arg#-verbose=}";;
		-depth=*)
			SUPERARG="${SUPERARG} -define DEPTH=${arg#-depth=}";;
		-osr=*)
			SUPERARG="${SUPERARG} -define OSR=${arg#-osr=}";;
		-out=*)
			SUPERARG="${SUPERARG} -define OUT_FILE=${arg#-out=}";;
		-define*)
			SUPERARG="${SUPERARG} ${arg}";;
		*)
			echo "Unknown argument" $arg;;
		esac
	done
fi

# Set default value
if [ -z ${TOP_MODULE} ]
then
	TOP_MODULE="TB_BATCH"
fi

SUPERARG="${SUPERARG} -top work.$TOP_MODULE"

if [ "$TOP_MODULE" = "TB_BATCH" ]
then
	TOP_FILE="TB_BATCH.sv"
elif [ "$TOP_MODULE" = "TB_FIR" ]
then
	TOP_FILE="TB_FIR.sv"
elif [ "$TOP_MODULE" = "TB_FIR_Fixed" ]
then
	TOP_FILE="TB_FIR_Fixed.sv"
elif [ "$TOP_MODULE" = "TB_BATCH_Fixed" ]
then
	TOP_FILE="TB_BATCH_Fixed.sv"
fi

if xrun -faccess +r -SV $SUPERARG -incdir ../sv/ -incdir ../sv/HardFloat-1/source/ $TOP_FILE
then
	echo "Success"
else
	echo "Failure"
	exit 1
fi
