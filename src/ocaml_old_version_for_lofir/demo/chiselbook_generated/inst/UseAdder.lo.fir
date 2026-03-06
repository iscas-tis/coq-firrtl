circuit UseAdder :
  module ParamAdder :
    input clock : Clock
    input reset1 : UInt<1>
    input io_a : UInt<8>
    input io_b : UInt<8>
    output io_c : UInt<8>

    node _io_c_T = add(io_a, io_b) @[ParamAdder.scala 11:16]
    node _io_c_T_1 = tail(_io_c_T, 1) @[ParamAdder.scala 11:16]
    io_c <= _io_c_T_1 @[ParamAdder.scala 11:8]

  module ParamAdder_1 :
    input clock : Clock
    input reset1 : UInt<1>
    input io_a : UInt<16>
    input io_b : UInt<16>
    output io_c : UInt<16>

    node _io_c_T = add(io_a, io_b) @[ParamAdder.scala 11:16]
    node _io_c_T_1 = tail(_io_c_T, 1) @[ParamAdder.scala 11:16]
    io_c <= _io_c_T_1 @[ParamAdder.scala 11:8]

  module UseAdder :
    input clock : Clock
    input reset1 : UInt<1>
    input io_x : UInt<16>
    input io_y : UInt<16>
    output io_res : UInt<16>

    inst add8 aof ParamAdder @[ParamAdder.scala 31:20]
    inst add16 aof ParamAdder_1 @[ParamAdder.scala 32:21]
    node _io_res_T = or(add16.io_c, add8.io_c) @[ParamAdder.scala 37:24]
    io_res <= _io_res_T @[ParamAdder.scala 37:10]
    add8.clock <= clock
    add8.reset1 <= reset1
    add8.io_a <= bits(io_x, 7, 0) @[ParamAdder.scala 39:13]
    add8.io_b <= bits(io_y, 7, 0) @[ParamAdder.scala 40:13]
    add16.clock <= clock
    add16.reset1 <= reset1
    add16.io_a <= io_x @[ParamAdder.scala 35:14]
    add16.io_b <= io_y @[ParamAdder.scala 36:14]
