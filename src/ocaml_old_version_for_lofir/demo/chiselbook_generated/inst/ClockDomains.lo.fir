circuit ClockDomains :
  module SourceClock :
    input clock : Clock
    input reset1 : UInt<1>
    output io_c_data : UInt<32>
    output io_c_valid : UInt<1>

    reg valid : UInt<1>, clock with :
      reset => (UInt<1>("h0"), valid) @[ClockDomains.scala 12:22]
    reg cntReg : UInt<32>, clock with :
      reset => (UInt<1>("h0"), cntReg) @[ClockDomains.scala 13:23]
    reg xReg : UInt<2>, clock with :
      reset => (UInt<1>("h0"), xReg) @[ClockDomains.scala 14:21]
    node _xReg_T = add(xReg, UInt<1>("h1")) @[ClockDomains.scala 15:16]
    node _xReg_T_1 = tail(_xReg_T, 1) @[ClockDomains.scala 15:16]
    node _valid_T = bits(xReg, 1, 1) @[ClockDomains.scala 17:16]
    node _falling_T = eq(valid, UInt<1>("h0")) @[ClockDomains.scala 18:17]
    reg falling_REG : UInt<1>, clock with :
      reset => (UInt<1>("h0"), falling_REG) @[ClockDomains.scala 18:33]
    node falling = and(_falling_T, falling_REG) @[ClockDomains.scala 18:24]
    node _cntReg_T = add(cntReg, UInt<1>("h1")) @[ClockDomains.scala 20:22]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[ClockDomains.scala 20:22]
    node _GEN_0 = mux(falling, _cntReg_T_1, cntReg) @[ClockDomains.scala 19:18 20:12 13:23]
    io_c_data <= cntReg @[ClockDomains.scala 23:13]
    io_c_valid <= valid @[ClockDomains.scala 22:14]
    valid <= mux(reset1, UInt<1>("h0"), _valid_T) @[ClockDomains.scala 12:{22,22} 17:9]
    cntReg <= mux(reset1, UInt<32>("h0"), _GEN_0) @[ClockDomains.scala 13:{23,23}]
    xReg <= mux(reset1, UInt<2>("h0"), _xReg_T_1) @[ClockDomains.scala 14:{21,21} 15:8]
    falling_REG <= valid @[ClockDomains.scala 18:33]

  module SinkClock :
    input clock : Clock
    input reset1 : UInt<1>
    input io_c_data : UInt<32>
    input io_c_valid : UInt<1>
    output io_errorCnt : UInt<8>

    reg expectedCntReg : UInt<32>, clock with :
      reset => (UInt<1>("h0"), expectedCntReg) @[ClockDomains.scala 42:31]
    reg errCntReg : UInt<8>, clock with :
      reset => (UInt<1>("h0"), errCntReg) @[ClockDomains.scala 43:26]
    reg sampleReg : UInt<32>, clock with :
      reset => (UInt<1>("h0"), sampleReg) @[ClockDomains.scala 44:26]
    reg rising_REG : UInt<1>, clock with :
      reset => (UInt<1>("h0"), rising_REG) @[ClockDomains.scala 46:37]
    node _rising_T = eq(rising_REG, UInt<1>("h0")) @[ClockDomains.scala 46:29]
    node rising = and(io_c_valid, _rising_T) @[ClockDomains.scala 46:27]
    node _T = neq(expectedCntReg, io_c_data) @[ClockDomains.scala 49:26]
    node _errCntReg_T = add(errCntReg, UInt<1>("h1")) @[ClockDomains.scala 50:30]
    node _errCntReg_T_1 = tail(_errCntReg_T, 1) @[ClockDomains.scala 50:30]
    node _GEN_0 = mux(_T, _errCntReg_T_1, errCntReg) @[ClockDomains.scala 49:41 50:17 43:26]
    node _expectedCntReg_T = add(expectedCntReg, UInt<1>("h1")) @[ClockDomains.scala 53:38]
    node _expectedCntReg_T_1 = tail(_expectedCntReg_T, 1) @[ClockDomains.scala 53:38]
    node _GEN_1 = mux(rising, _GEN_0, errCntReg) @[ClockDomains.scala 48:17 43:26]
    node _GEN_2 = mux(rising, io_c_data, sampleReg) @[ClockDomains.scala 48:17 52:15 44:26]
    node _GEN_3 = mux(rising, _expectedCntReg_T_1, expectedCntReg) @[ClockDomains.scala 48:17 53:20 42:31]
    io_errorCnt <= errCntReg @[ClockDomains.scala 56:15]
    expectedCntReg <= mux(reset1, UInt<32>("h0"), _GEN_3) @[ClockDomains.scala 42:{31,31}]
    errCntReg <= mux(reset1, UInt<8>("h0"), _GEN_1) @[ClockDomains.scala 43:{26,26}]
    sampleReg <= mux(reset1, UInt<32>("h0"), _GEN_2) @[ClockDomains.scala 44:{26,26}]
    rising_REG <= io_c_valid @[ClockDomains.scala 46:37]

  module ClockDomains :
    input clock : Clock
    input reset1 : UInt<1>
    output io_errCnt : UInt<8>

    inst s aof SourceClock @[ClockDomains.scala 73:17]
    inst d aof SinkClock @[ClockDomains.scala 74:17]
    io_errCnt <= d.io_errorCnt @[ClockDomains.scala 77:13]
    s.clock <= clock
    s.reset1 <= reset1
    d.clock <= clock
    d.reset1 <= reset1
    d.io_c_data <= s.io_c_data @[ClockDomains.scala 76:10]
    d.io_c_valid <= s.io_c_valid @[ClockDomains.scala 76:10]
