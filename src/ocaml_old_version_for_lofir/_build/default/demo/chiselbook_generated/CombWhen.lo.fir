circuit CombWhen :
  module CombWhen :
    input clock : Clock
    input reset1 : UInt<1>
    input io_cond : UInt<1>
    output io_out : UInt<4>

    node _GEN_0 = mux(io_cond, UInt<2>("h3"), UInt<1>("h0")) @[Combinational.scala 53:15 52:5 54:7]
    node w = _GEN_0 @[Combinational.scala 50:15]
    io_out <= pad(w, 4) @[Combinational.scala 57:10]
