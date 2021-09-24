rm -rf work*

RED='\033[0;31m'
NC='\033[0m'    

printf "${RED}\nCompiling and Simulating${NC}\n"
if [[ "$@" =~ -gui ]]
then
	xrun -gui -faccess +r -SV -top work.TB -define MANT_W=12 -define EXP_W=8 -define INCLUDE_RAM -incdir ../sv/ -incdir ../sv/HardFloat-1/source/ ./*.sv
else
	if xrun -faccess +r -SV -top work.TB -define MANT_W=12 -define EXP_W=8 -define INCLUDE_RAM -incdir ../sv/ -incdir ../sv/HardFloat-1/source/ ./*.sv
	then
		echo "Success"
	else
		echo "Failure"
		exit 1
	fi
fi