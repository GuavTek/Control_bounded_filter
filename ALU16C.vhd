library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity ALU16C is
    port(
        A, B    : in std_logic_vector(31 downto 0);
        func    : in std_logic_vector(1 downto 0);
        R       : out std_logic_vector(31 downto 0)
    );
end entity;

architecture arc of ALU16C is
subtype floatType is float(5 downto -10);
signal Afr, Afi, Bfr, Bfi, Rfr, Rfi : floatType;
begin

    R[15:0] <= to_slv(Rfr);
    R[31:16] <= to_slv(Rfi);
    Afr <= to_float(A[15:0], Afr);
    Afi <= to_float(A[31:16], Afi);
    Bfr <= to_float(B[15:0], Bfr);
    Bfi <= to_float(B[31:16], Bfi);

    with func select Rfr <=
        Afr + Bfr when "00",
        Afr - Bfr when "01",
        (Afr * Bfr) + (Afi * Bfi) when others;

    with func select Rfi <=
        Afi + Bfi when "00",
        Afi - Bfi when "01",
        (Afr * Bfi) + (Afi * Bfr) when others;

end architecture;