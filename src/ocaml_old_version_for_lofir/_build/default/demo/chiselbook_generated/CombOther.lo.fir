circuit CombOther :
  module CombOther :
    input clock : Clock
    input reset1 : UInt<1>
    input io_cond : UInt<1>
    output io_out : UInt<4>

    node _GEN_0 = mux(io_cond, UInt<1>("h1"), UInt<2>("h2")) @[Combinational.scala 105:15 106:7 108:7]
    node w = _GEN_0 @[Combinational.scala 103:15]
    io_out <= pad(w, 4) @[Combinational.scala 111:10]
