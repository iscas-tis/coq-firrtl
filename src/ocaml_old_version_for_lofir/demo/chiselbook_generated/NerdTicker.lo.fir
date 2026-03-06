circuit NerdTicker :
  module NerdTicker :
    input clock : Clock
    input reset1 : UInt<1>
    output io_tick : UInt<1>

    reg cntReg : SInt<8>, clock with :
      reset => (UInt<1>("h0"), cntReg) @[Ticker.scala 66:23]
    node _cntReg_T = sub(cntReg, asSInt(UInt<2>("h1"))) @[Ticker.scala 69:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Ticker.scala 69:20]
    node _cntReg_T_2 = asSInt(_cntReg_T_1) @[Ticker.scala 69:20]
    node _T = bits(cntReg, 7, 7) @[Ticker.scala 70:14]
    node _GEN_0 = mux(_T, asSInt(UInt<8>("h6")), _cntReg_T_2) @[Ticker.scala 69:10 70:19 71:12]
    node _GEN_1 = mux(_T, UInt<1>("h1"), UInt<1>("h0")) @[Ticker.scala 67:11 70:19 72:13]
    io_tick <= _GEN_1
    cntReg <= mux(reset1, asSInt(UInt<8>("h6")), _GEN_0) @[Ticker.scala 66:{23,23}]
