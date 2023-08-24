circuit Accumulator : 
  module Accumulator : 
    input clock : Clock 
    input reset1 : UInt<1> 
    input io_in : UInt<4> 
    output io_out : UInt<8> 

    reg accumulator : UInt<8>, clock with :
      reset => (UInt<1>("h0"), accumulator) 
    node _T_11 = add(accumulator, io_in) 
    node _T_12 = tail(_T_11, 1) 
    accumulator <= mux(reset1, UInt<8>("h0"), _T_12) 
    io_out <= accumulator 
    
