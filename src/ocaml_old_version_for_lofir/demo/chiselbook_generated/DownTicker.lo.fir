circuit DownTicker :
  module DownTicker :
    input clock : Clock
    input reset1 : UInt<1>
    output io_tick : UInt<1>

    reg cntReg : UInt<3>, clock with :
      reset => (UInt<1>("h0"), cntReg) @[Ticker.scala 41:23]
    node _cntReg_T = sub(cntReg, UInt<1>("h1")) @[Ticker.scala 43:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Ticker.scala 43:20]
    node _T = eq(cntReg, UInt<1>("h0")) @[Ticker.scala 44:15]
    node _GEN_0 = mux(_T, UInt<3>("h7"), _cntReg_T_1) @[Ticker.scala 43:10 44:24 45:12]
    node _io_tick_T = eq(cntReg, UInt<3>("h7")) @[Ticker.scala 48:21]
    io_tick <= _io_tick_T @[Ticker.scala 48:11]
    cntReg <= mux(reset1, UInt<3>("h7"), _GEN_0) @[Ticker.scala 41:{23,23}]
