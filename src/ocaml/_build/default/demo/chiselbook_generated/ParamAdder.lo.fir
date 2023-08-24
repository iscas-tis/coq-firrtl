circuit ParamAdder :
  module ParamAdder :
    input clock : Clock
    input reset1 : UInt<1>
    input io_a : UInt<8>
    input io_b : UInt<8>
    output io_c : UInt<8>

    node _io_c_T = add(io_a, io_b) @[ParamAdder.scala 11:16]
    node _io_c_T_1 = tail(_io_c_T, 1) @[ParamAdder.scala 11:16]
    io_c <= _io_c_T_1 @[ParamAdder.scala 11:8]
