circuit Arbiter3Direct :
  module Arbiter3Direct :
    input clock : Clock
    input reset1 : UInt<1>
    input io_request : UInt<3>
    output io_grant : UInt<3>

    node _T = eq(UInt<1>("h0"), io_request) @[arbiter.scala 45:20]
    node _T_1 = eq(UInt<1>("h1"), io_request) @[arbiter.scala 45:20]
    node _T_2 = eq(UInt<2>("h2"), io_request) @[arbiter.scala 45:20]
    node _T_3 = eq(UInt<2>("h3"), io_request) @[arbiter.scala 45:20]
    node _T_4 = eq(UInt<3>("h4"), io_request) @[arbiter.scala 45:20]
    node _T_5 = eq(UInt<3>("h5"), io_request) @[arbiter.scala 45:20]
    node _T_6 = eq(UInt<3>("h6"), io_request) @[arbiter.scala 45:20]
    node _T_7 = eq(UInt<3>("h7"), io_request) @[arbiter.scala 45:20]
    node _GEN_0 = mux(_T_7, UInt<1>("h1"), UInt<3>("h0")) @[arbiter.scala 45:20 44:26 53:27]
    node _GEN_1 = mux(_T_6, UInt<2>("h2"), _GEN_0) @[arbiter.scala 45:20 52:27]
    node _GEN_2 = mux(_T_5, UInt<1>("h1"), _GEN_1) @[arbiter.scala 45:20 51:27]
    node _GEN_3 = mux(_T_4, UInt<3>("h4"), _GEN_2) @[arbiter.scala 45:20 50:27]
    node _GEN_4 = mux(_T_3, UInt<1>("h1"), _GEN_3) @[arbiter.scala 45:20 49:27]
    node _GEN_5 = mux(_T_2, UInt<2>("h2"), _GEN_4) @[arbiter.scala 45:20 48:27]
    node _GEN_6 = mux(_T_1, UInt<1>("h1"), _GEN_5) @[arbiter.scala 45:20 47:27]
    node _GEN_7 = mux(_T, UInt<1>("h0"), _GEN_6) @[arbiter.scala 45:20 46:27]
    node grant = _GEN_7 @[arbiter.scala 44:26]
    io_grant <= grant @[arbiter.scala 56:12]
