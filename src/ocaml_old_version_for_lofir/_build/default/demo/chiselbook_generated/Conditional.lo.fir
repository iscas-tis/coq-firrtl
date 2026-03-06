circuit Conditional :
  module Conditional :
    input clock : Clock
    input reset1 : UInt<1>
    input io_condition : UInt<1>
    output io_result : UInt<4>

    node c1 = eq(io_condition, UInt<1>("h0")) @[Snippets.scala 91:12]
    node c2 = eq(io_condition, UInt<1>("h0")) @[Snippets.scala 92:12]
    node _GEN_0 = mux(io_condition, UInt<1>("h0"), UInt<3>("h5")) @[Snippets.scala 97:20 96:5 98:7]
    node _GEN_1 = mux(c1, UInt<1>("h1"), _GEN_0) @[Snippets.scala 101:{13,17}]
    node _GEN_2 = mux(c2, UInt<2>("h2"), _GEN_1) @[Snippets.scala 102:{13,17}]
    node _GEN_3 = mux(c2, UInt<2>("h2"), UInt<2>("h3")) @[Snippets.scala 105:{20,24} 106:20]
    node _GEN_4 = mux(c1, UInt<1>("h1"), _GEN_3) @[Snippets.scala 104:{13,17}]
    node v = pad(_GEN_4, 3) @[Snippets.scala 94:15]
    io_result <= pad(v, 4) @[Snippets.scala 108:13]
