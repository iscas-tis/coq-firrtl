circuit Combinational :
  module Combinational :
    input clock : Clock
    input reset1 : UInt<1>
    input io_a : UInt<4>
    input io_b : UInt<4>
    input io_c : UInt<4>
    output io_out : UInt<4>
    output io_out2 : UInt<4>

    node _e_T = and(io_a, io_b) @[Combinational.scala 17:14]
    node e = or(_e_T, io_c) @[Combinational.scala 17:19]
    node f = not(e) @[Combinational.scala 21:11]
    io_out <= e @[Combinational.scala 30:10]
    io_out2 <= f @[Combinational.scala 31:11]
