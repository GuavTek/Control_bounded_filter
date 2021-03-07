use library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use IEEE.float_pkg.all;

entity ALU16 is
    port(
        A, B    : in std_logic_vector(15 downto 0);
        func    : in std_logic_vector(1 downto 0);
        R       : out std_logic_vector(15 downto 0)
    );
end entity;

architecture arc of ALU16 is
subtype float16 is float(5 downto -10);
signal Af, Bf, Rf : float16;
begin

    R <= to_slv(Rf);
    Af <= to_float(A, Af);
    Bf <= to_float(B, Bf);

    with func select Rf <=
        Af + Bf when "00",
        Af - Bf when "01",
        Af * Bf when others;

end architecture;