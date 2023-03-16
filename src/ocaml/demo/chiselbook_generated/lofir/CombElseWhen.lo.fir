circuit CombElseWhen :
  module CombElseWhen :
    input clock : Clock
    input reset1 : UInt<1>
    input io_cond : UInt<1>
    input io_cond2 : UInt<1>
    output io_out : UInt<4>

    node _GEN_0 = mux(io_cond2, UInt<2>("h2"), UInt<2>("h3")) @[Combinational.scala 137:23 138:7 140:7]
    node _GEN_1 = mux(io_cond, UInt<1>("h1"), _GEN_0) @[Combinational.scala 135:15 136:7]
    node w = _GEN_1 @[Combinational.scala 133:15]
    io_out <= pad(w, 4) @[Combinational.scala 143:10]
