circuit CountBool :
  module CountBool :
    input clock : Clock
    input reset1 : UInt<1>
    input io_in_0 : UInt<1>
    input io_in_1 : UInt<1>
    input io_in_2 : UInt<1>
    input io_in_3 : UInt<1>
    input io_in_4 : UInt<1>
    input io_in_5 : UInt<1>
    input io_in_6 : UInt<1>
    input io_in_7 : UInt<1>
    input io_in_8 : UInt<1>
    output io_out : UInt<4>

    node _io_out_T = add(io_in_0, io_in_1) @[Bitwise.scala 51:90]
    node _io_out_T_1 = bits(_io_out_T, 1, 0) @[Bitwise.scala 51:90]
    node _io_out_T_2 = add(io_in_2, io_in_3) @[Bitwise.scala 51:90]
    node _io_out_T_3 = bits(_io_out_T_2, 1, 0) @[Bitwise.scala 51:90]
    node _io_out_T_4 = add(_io_out_T_1, _io_out_T_3) @[Bitwise.scala 51:90]
    node _io_out_T_5 = bits(_io_out_T_4, 2, 0) @[Bitwise.scala 51:90]
    node _io_out_T_6 = add(io_in_4, io_in_5) @[Bitwise.scala 51:90]
    node _io_out_T_7 = bits(_io_out_T_6, 1, 0) @[Bitwise.scala 51:90]
    node _io_out_T_8 = add(io_in_7, io_in_8) @[Bitwise.scala 51:90]
    node _io_out_T_9 = bits(_io_out_T_8, 1, 0) @[Bitwise.scala 51:90]
    node _io_out_T_10 = add(io_in_6, _io_out_T_9) @[Bitwise.scala 51:90]
    node _io_out_T_11 = bits(_io_out_T_10, 1, 0) @[Bitwise.scala 51:90]
    node _io_out_T_12 = add(_io_out_T_7, _io_out_T_11) @[Bitwise.scala 51:90]
    node _io_out_T_13 = bits(_io_out_T_12, 2, 0) @[Bitwise.scala 51:90]
    node _io_out_T_14 = add(_io_out_T_5, _io_out_T_13) @[Bitwise.scala 51:90]
    node _io_out_T_15 = bits(_io_out_T_14, 3, 0) @[Bitwise.scala 51:90]
    io_out <= _io_out_T_15 @[CountBool.scala 10:10]
