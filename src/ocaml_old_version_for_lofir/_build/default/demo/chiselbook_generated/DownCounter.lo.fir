circuit DownCounter :
  module DownCounter :
    input clock : Clock
    input reset1 : UInt<1>
    output io_cnt : UInt<8>
    output io_tick : UInt<1>

    reg cntReg : UInt<3>, clock with :
      reset => (UInt<1>("h0"), cntReg) @[Counter.scala 88:23]
    node _cntReg_T = sub(cntReg, UInt<1>("h1")) @[Counter.scala 90:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Counter.scala 90:20]
    node _T = eq(cntReg, UInt<1>("h0")) @[Counter.scala 91:15]
    node _GEN_0 = mux(_T, UInt<3>("h7"), _cntReg_T_1) @[Counter.scala 90:10 91:24 92:12]
    node _io_tick_T = eq(cntReg, UInt<1>("h0")) @[Counter.scala 96:21]
    io_cnt <= pad(cntReg, 8) @[Counter.scala 97:10]
    io_tick <= _io_tick_T @[Counter.scala 96:11]
    cntReg <= mux(reset1, UInt<3>("h7"), _GEN_0) @[Counter.scala 88:{23,23}]
