circuit CombWireDefault :
  module CombWireDefault :
    input clock : Clock
    input reset1 : UInt<1>
    input io_cond : UInt<1>
    output io_out : UInt<4>

    node _GEN_0 = mux(io_cond, UInt<2>("h3"), UInt<1>("h0")) @[Combinational.scala 165:15 163:22 166:7]
    node w = _GEN_0 @[Combinational.scala 163:22]
    io_out <= pad(w, 4) @[Combinational.scala 170:10]
