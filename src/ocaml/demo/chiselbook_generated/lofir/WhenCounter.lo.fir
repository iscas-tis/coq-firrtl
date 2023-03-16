circuit WhenCounter :
  module WhenCounter :
    input clock : Clock
    input reset1 : UInt<1>
    output io_cnt : UInt<8>
    output io_tick : UInt<1>

    reg cntReg : UInt<8>, clock with :
      reset => (UInt<1>("h0"), cntReg) @[Counter.scala 38:23]
    node _cntReg_T = add(cntReg, UInt<1>("h1")) @[Counter.scala 40:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Counter.scala 40:20]
    node _T = eq(cntReg, UInt<3>("h7")) @[Counter.scala 41:15]
    node _GEN_0 = mux(_T, UInt<1>("h0"), _cntReg_T_1) @[Counter.scala 40:10 41:22 42:12]
    node _io_tick_T = eq(cntReg, UInt<3>("h7")) @[Counter.scala 46:21]
    io_cnt <= cntReg @[Counter.scala 47:10]
    io_tick <= _io_tick_T @[Counter.scala 46:11]
    cntReg <= mux(reset1, UInt<8>("h0"), _GEN_0) @[Counter.scala 38:{23,23}]
