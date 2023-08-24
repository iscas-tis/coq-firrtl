circuit DrawMux6 :
  module DrawMux6 :
    input clock : Clock
    input reset1 : UInt<1>
    input io_sel : UInt<3>
    output io_dout : UInt<8>

    node _T = eq(UInt<1>("h0"), io_sel) @[drawing.scala 50:15]
    node _T_1 = eq(UInt<1>("h1"), io_sel) @[drawing.scala 50:15]
    node _T_2 = eq(UInt<2>("h2"), io_sel) @[drawing.scala 50:15]
    node _T_3 = eq(UInt<2>("h3"), io_sel) @[drawing.scala 50:15]
    node _T_4 = eq(UInt<3>("h4"), io_sel) @[drawing.scala 50:15]
    node _T_5 = eq(UInt<3>("h5"), io_sel) @[drawing.scala 50:15]
    node _GEN_0 = mux(_T_5, UInt<6>("h37"), UInt<1>("h0")) @[drawing.scala 50:15 56:20 48:25]
    node _GEN_1 = mux(_T_4, UInt<6>("h2c"), _GEN_0) @[drawing.scala 50:15 55:20]
    node _GEN_2 = mux(_T_3, UInt<6>("h21"), _GEN_1) @[drawing.scala 50:15 54:20]
    node _GEN_3 = mux(_T_2, UInt<5>("h16"), _GEN_2) @[drawing.scala 50:15 53:20]
    node _GEN_4 = mux(_T_1, UInt<4>("hb"), _GEN_3) @[drawing.scala 50:15 52:20]
    node _GEN_5 = mux(_T, UInt<1>("h0"), _GEN_4) @[drawing.scala 50:15 51:20]
    node dout = _GEN_5 @[drawing.scala 48:25]
    io_dout <= pad(dout, 8) @[drawing.scala 60:11]
