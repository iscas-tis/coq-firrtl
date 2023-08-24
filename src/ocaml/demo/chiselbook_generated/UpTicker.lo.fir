circuit UpTicker :
  module UpTicker :
    input clock : Clock
    input reset1 : UInt<1>
    output io_tick : UInt<1>

    reg cntReg : UInt<8>, clock with :
      reset => (UInt<1>("h0"), cntReg) @[Ticker.scala 16:23]
    node _cntReg_T = add(cntReg, UInt<1>("h1")) @[Ticker.scala 18:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Ticker.scala 18:20]
    node tick = eq(cntReg, UInt<3>("h7")) @[Ticker.scala 19:21]
    node _GEN_0 = mux(tick, UInt<1>("h0"), _cntReg_T_1) @[Ticker.scala 18:10 20:14 21:12]
    io_tick <= tick @[Ticker.scala 24:11]
    cntReg <= mux(reset1, UInt<8>("h0"), _GEN_0) @[Ticker.scala 16:{23,23}]
