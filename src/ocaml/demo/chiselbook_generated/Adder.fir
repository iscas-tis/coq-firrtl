circuit Adder :
  module Adder :
    input clock : Clock
    input reset : UInt<1>
    output io : { flip a : UInt<8>, flip b : UInt<8>, y : UInt<8>}

    node _io_y_T = add(io.a, io.b) @[components.scala 15:16]
    node _io_y_T_1 = tail(_io_y_T, 1) @[components.scala 15:16]
    io.y <= _io_y_T_1 @[components.scala 15:8]

