circuit SinkClock :
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
