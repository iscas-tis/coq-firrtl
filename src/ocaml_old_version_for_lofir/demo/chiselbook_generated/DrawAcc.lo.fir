circuit DrawAcc :
  module DrawAcc :
    input clock : Clock
    input reset1 : UInt<1>
    input io_din : UInt<8>
    input io_sel : UInt<3>
    output io_dout : UInt<8>

    reg regAcc : UInt<8>, clock with :
      reset => (UInt<1>("h0"), regAcc) @[drawing.scala 17:23]
    node _T = eq(UInt<1>("h0"), io_sel) @[drawing.scala 19:15]
    node _T_1 = eq(UInt<1>("h1"), io_sel) @[drawing.scala 19:15]
    node _T_2 = eq(UInt<2>("h2"), io_sel) @[drawing.scala 19:15]
    node _regAcc_T = add(regAcc, io_din) @[drawing.scala 22:32]
    node _regAcc_T_1 = tail(_regAcc_T, 1) @[drawing.scala 22:32]
    node _T_3 = eq(UInt<2>("h3"), io_sel) @[drawing.scala 19:15]
    node _regAcc_T_2 = sub(regAcc, io_din) @[drawing.scala 23:32]
    node _regAcc_T_3 = tail(_regAcc_T_2, 1) @[drawing.scala 23:32]
    node _GEN_0 = mux(_T_3, _regAcc_T_3, regAcc) @[drawing.scala 19:15 23:22 17:23]
    node _GEN_1 = mux(_T_2, _regAcc_T_1, _GEN_0) @[drawing.scala 19:15 22:22]
    node _GEN_2 = mux(_T_1, UInt<1>("h0"), _GEN_1) @[drawing.scala 19:15 21:22]
    node _GEN_3 = mux(_T, regAcc, _GEN_2) @[drawing.scala 19:15 20:22]
    io_dout <= regAcc @[drawing.scala 27:11]
    regAcc <= mux(reset1, UInt<8>("h0"), _GEN_3) @[drawing.scala 17:{23,23}]
