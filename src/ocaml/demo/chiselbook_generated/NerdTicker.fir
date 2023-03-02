circuit NerdTicker :
  module NerdTicker :
    input clock : Clock
    input reset : UInt<1>
    output io : { tick : UInt<1>}

    reg cntReg : SInt<8>, clock with :
      reset => (reset, asSInt(UInt<8>("h6"))) @[Ticker.scala 66:23]
    io.tick <= UInt<1>("h0") @[Ticker.scala 67:11]
    node _cntReg_T = sub(cntReg, asSInt(UInt<2>("h1"))) @[Ticker.scala 69:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Ticker.scala 69:20]
    node _cntReg_T_2 = asSInt(_cntReg_T_1) @[Ticker.scala 69:20]
    cntReg <= _cntReg_T_2 @[Ticker.scala 69:10]
    node _T = bits(cntReg, 7, 7) @[Ticker.scala 70:14]
    when _T : @[Ticker.scala 70:19]
      cntReg <= asSInt(UInt<8>("h6")) @[Ticker.scala 71:12]
      io.tick <= UInt<1>("h1") @[Ticker.scala 72:13]


