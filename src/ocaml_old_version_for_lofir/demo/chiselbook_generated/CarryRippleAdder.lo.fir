circuit CarryRippleAdder :
  module CarryRippleAdder :
    input clock : Clock
    input reset1 : UInt<1>
    input io_a : UInt<32>
    input io_b : UInt<32>
    input io_cin : UInt<1>
    output io_c : UInt<32>
    output io_cout : UInt<1>

    node _aOp_WIRE = io_a @[Adders.scala 19:{13,13}]
    node _aOp_T = bits(_aOp_WIRE, 3, 0) @[Adders.scala 19:13]
    node _aOp_T_1 = bits(_aOp_WIRE, 7, 4) @[Adders.scala 19:13]
    node _aOp_T_2 = bits(_aOp_WIRE, 11, 8) @[Adders.scala 19:13]
    node _aOp_T_3 = bits(_aOp_WIRE, 15, 12) @[Adders.scala 19:13]
    node _aOp_T_4 = bits(_aOp_WIRE, 19, 16) @[Adders.scala 19:13]
    node _aOp_T_5 = bits(_aOp_WIRE, 23, 20) @[Adders.scala 19:13]
    node _aOp_T_6 = bits(_aOp_WIRE, 27, 24) @[Adders.scala 19:13]
    node _aOp_T_7 = bits(_aOp_WIRE, 31, 28) @[Adders.scala 19:13]
    node _bOp_WIRE = io_b @[Adders.scala 22:{13,13}]
    node _bOp_T = bits(_bOp_WIRE, 3, 0) @[Adders.scala 22:13]
    node _bOp_T_1 = bits(_bOp_WIRE, 7, 4) @[Adders.scala 22:13]
    node _bOp_T_2 = bits(_bOp_WIRE, 11, 8) @[Adders.scala 22:13]
    node _bOp_T_3 = bits(_bOp_WIRE, 15, 12) @[Adders.scala 22:13]
    node _bOp_T_4 = bits(_bOp_WIRE, 19, 16) @[Adders.scala 22:13]
    node _bOp_T_5 = bits(_bOp_WIRE, 23, 20) @[Adders.scala 22:13]
    node _bOp_T_6 = bits(_bOp_WIRE, 27, 24) @[Adders.scala 22:13]
    node _bOp_T_7 = bits(_bOp_WIRE, 31, 28) @[Adders.scala 22:13]
    node _res_T = add(io_a, io_b) @[Adders.scala 26:18]
    node _res_T_1 = add(_res_T, io_cin) @[Adders.scala 26:26]
    node res = tail(_res_T_1, 1) @[Adders.scala 26:26]
    node _io_c_T = bits(res, 31, 0) @[Adders.scala 27:17]
    node _io_cout_T = bits(res, 32, 32) @[Adders.scala 28:17]
    node aOp_0 = _aOp_T @[Adders.scala 19:{13,13}]
    node aOp_1 = _aOp_T_1 @[Adders.scala 19:{13,13}]
    node aOp_2 = _aOp_T_2 @[Adders.scala 19:{13,13}]
    node aOp_3 = _aOp_T_3 @[Adders.scala 19:{13,13}]
    node aOp_4 = _aOp_T_4 @[Adders.scala 19:{13,13}]
    node aOp_5 = _aOp_T_5 @[Adders.scala 19:{13,13}]
    node aOp_6 = _aOp_T_6 @[Adders.scala 19:{13,13}]
    node aOp_7 = _aOp_T_7 @[Adders.scala 19:{13,13}]
    node bOp_0 = _bOp_T @[Adders.scala 22:{13,13}]
    node bOp_1 = _bOp_T_1 @[Adders.scala 22:{13,13}]
    node bOp_2 = _bOp_T_2 @[Adders.scala 22:{13,13}]
    node bOp_3 = _bOp_T_3 @[Adders.scala 22:{13,13}]
    node bOp_4 = _bOp_T_4 @[Adders.scala 22:{13,13}]
    node bOp_5 = _bOp_T_5 @[Adders.scala 22:{13,13}]
    node bOp_6 = _bOp_T_6 @[Adders.scala 22:{13,13}]
    node bOp_7 = _bOp_T_7 @[Adders.scala 22:{13,13}]
    io_c <= _io_c_T @[Adders.scala 27:11]
    io_cout <= _io_cout_T @[Adders.scala 28:11]
