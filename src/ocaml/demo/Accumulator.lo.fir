circuit Accumulator : @[:@2.0]
  module Accumulator : @[:@3.2]
    input clock : Clock @[:@4.4]
    input reset1 : UInt<1> @[:@5.4]
    input io_in : UInt<4> @[:@6.4]
    output io_out : UInt<8> @[:@6.4]

    reg accumulator : UInt<8>, clock with :
      reset => (UInt<1>("h0"), accumulator) @[Accumulator.scala 16:28:@8.4]
    node _T_11 = add(accumulator, io_in) @[Accumulator.scala 17:30:@9.4]
    node _T_12 = tail(_T_11, 1) @[Accumulator.scala 17:30:@10.4]
    accumulator <= mux(reset1, UInt<8>("h0"), _T_12) @[Accumulator.scala 17:15:@11.4]
    io_out <= accumulator @[Accumulator.scala 18:10:@12.4]
    
