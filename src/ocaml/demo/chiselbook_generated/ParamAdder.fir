circuit ParamAdder :
  module ParamAdder :
    input clock : Clock
    input reset : UInt<1>
    output io : { flip a : UInt<8>, flip b : UInt<8>, c : UInt<8>}

    node _io_c_T = add(io.a, io.b) @[ParamAdder.scala 11:16]
    node _io_c_T_1 = tail(_io_c_T, 1) @[ParamAdder.scala 11:16]
    io.c <= _io_c_T_1 @[ParamAdder.scala 11:8]

