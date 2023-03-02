circuit DownTicker :
  module DownTicker :
    input clock : Clock
    input reset : UInt<1>
    output io : { tick : UInt<1>}

    reg cntReg : UInt, clock with :
      reset => (reset, UInt<3>("h7")) @[Ticker.scala 41:23]
    node _cntReg_T = sub(cntReg, UInt<1>("h1")) @[Ticker.scala 43:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Ticker.scala 43:20]
    cntReg <= _cntReg_T_1 @[Ticker.scala 43:10]
    node _T = eq(cntReg, UInt<1>("h0")) @[Ticker.scala 44:15]
    when _T : @[Ticker.scala 44:24]
      cntReg <= UInt<3>("h7") @[Ticker.scala 45:12]
    node _io_tick_T = eq(cntReg, UInt<3>("h7")) @[Ticker.scala 48:21]
    io.tick <= _io_tick_T @[Ticker.scala 48:11]

