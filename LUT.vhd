use library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use IEEE.float_pkg.all;

entity LUT is
    generic(
		re	: real; 
		im	: real
	);
	port(
        sel 	: in std_logic;
        Result	: out std_logic_vector(31 downto 0)
    );
end entity;

architecture arc of LUT is
subtype float16 is float(5 downto -10);
signal Rr, Ri : float16;
signal rePol, imPol : real;
begin
	-- Output results
	Result[15:0] <= to_slv(Rr);
    Result[31:16] <= to_slv(Ri);

	-- Select polarity
	rePol <= 	re when sel = 1 else
				-re;
	imPol <=	im when sel = 1 else
				-im;
	
	-- Format the results
	Rr <= to_float(rePol, Rr);
	Ri <= to_float(imPol, Ri);
end architecture;