circuit Adder :
  module Adder :
    input clock : Clock
    input reset1 : UInt<1>
    input io_a : UInt<8>
    input io_b : UInt<8>
    output io_y : UInt<8>

    node _io_y_T = add(io_a, io_b) @[components.scala 15:16]
    node _io_y_T_1 = tail(_io_y_T, 1) @[components.scala 15:16]
    io_y <= _io_y_T_1 @[components.scala 15:8]
