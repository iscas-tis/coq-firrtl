circuit ClockDomains :
  module SourceClock :
    input clock : Clock
    input reset : Reset
    output io : { c : { data : UInt<32>, valid : UInt<1>}}

    reg valid : UInt<1>, clock with :
      reset => (reset, UInt<1>("h0")) @[ClockDomains.scala 12:22]
    reg cntReg : UInt<32>, clock with :
      reset => (reset, UInt<32>("h0")) @[ClockDomains.scala 13:23]
    reg xReg : UInt<2>, clock with :
      reset => (reset, UInt<2>("h0")) @[ClockDomains.scala 14:21]
    node _xReg_T = add(xReg, UInt<1>("h1")) @[ClockDomains.scala 15:16]
    node _xReg_T_1 = tail(_xReg_T, 1) @[ClockDomains.scala 15:16]
    xReg <= _xReg_T_1 @[ClockDomains.scala 15:8]
    node _valid_T = bits(xReg, 1, 1) @[ClockDomains.scala 17:16]
    valid <= _valid_T @[ClockDomains.scala 17:9]
    node _falling_T = eq(valid, UInt<1>("h0")) @[ClockDomains.scala 18:17]
    reg falling_REG : UInt<1>, clock with :
      reset => (UInt<1>("h0"), falling_REG) @[ClockDomains.scala 18:33]
    falling_REG <= valid @[ClockDomains.scala 18:33]
    node falling = and(_falling_T, falling_REG) @[ClockDomains.scala 18:24]
    when falling : @[ClockDomains.scala 19:18]
      node _cntReg_T = add(cntReg, UInt<1>("h1")) @[ClockDomains.scala 20:22]
      node _cntReg_T_1 = tail(_cntReg_T, 1) @[ClockDomains.scala 20:22]
      cntReg <= _cntReg_T_1 @[ClockDomains.scala 20:12]
    io.c.valid <= valid @[ClockDomains.scala 22:14]
    io.c.data <= cntReg @[ClockDomains.scala 23:13]

  module SinkClock :
    input clock : Clock
    input reset : Reset
    output io : { flip c : { data : UInt<32>, valid : UInt<1>}, errorCnt : UInt<8>}

    reg expectedCntReg : UInt<32>, clock with :
      reset => (reset, UInt<32>("h0")) @[ClockDomains.scala 42:31]
    reg errCntReg : UInt<8>, clock with :
      reset => (reset, UInt<8>("h0")) @[ClockDomains.scala 43:26]
    reg sampleReg : UInt<32>, clock with :
      reset => (reset, UInt<32>("h0")) @[ClockDomains.scala 44:26]
    reg rising_REG : UInt<1>, clock with :
      reset => (UInt<1>("h0"), rising_REG) @[ClockDomains.scala 46:37]
    rising_REG <= io.c.valid @[ClockDomains.scala 46:37]
    node _rising_T = eq(rising_REG, UInt<1>("h0")) @[ClockDomains.scala 46:29]
    node rising = and(io.c.valid, _rising_T) @[ClockDomains.scala 46:27]
    when rising : @[ClockDomains.scala 48:17]
      node _T = neq(expectedCntReg, io.c.data) @[ClockDomains.scala 49:26]
      when _T : @[ClockDomains.scala 49:41]
        node _errCntReg_T = add(errCntReg, UInt<1>("h1")) @[ClockDomains.scala 50:30]
        node _errCntReg_T_1 = tail(_errCntReg_T, 1) @[ClockDomains.scala 50:30]
        errCntReg <= _errCntReg_T_1 @[ClockDomains.scala 50:17]
      sampleReg <= io.c.data @[ClockDomains.scala 52:15]
      node _expectedCntReg_T = add(expectedCntReg, UInt<1>("h1")) @[ClockDomains.scala 53:38]
      node _expectedCntReg_T_1 = tail(_expectedCntReg_T, 1) @[ClockDomains.scala 53:38]
      expectedCntReg <= _expectedCntReg_T_1 @[ClockDomains.scala 53:20]
    io.errorCnt <= errCntReg @[ClockDomains.scala 56:15]

  module ClockDomains :
    input clock : Clock
    input reset : UInt<1>
    output io : { errCnt : UInt<8>}

    inst s of SourceClock @[ClockDomains.scala 73:17]
    s.clock <= clock
    s.reset <= reset
    inst d of SinkClock @[ClockDomains.scala 74:17]
    d.clock <= clock
    d.reset <= reset
    d.io.c <= s.io.c @[ClockDomains.scala 76:10]
    io.errCnt <= d.io.errorCnt @[ClockDomains.scala 77:13]

