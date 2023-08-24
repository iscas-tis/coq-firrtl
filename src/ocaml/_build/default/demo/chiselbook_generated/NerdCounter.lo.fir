circuit NerdCounter :
  module NerdCounter :
    input clock : Clock
    input reset1 : UInt<1>
    output io_cnt : UInt<8>
    output io_tick : UInt<1>

    reg cntReg : SInt<8>, clock with :
      reset => (UInt<1>("h0"), cntReg) @[Counter.scala 144:23]
    node _cntReg_T = sub(cntReg, asSInt(UInt<2>("h1"))) @[Counter.scala 147:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Counter.scala 147:20]
    node _cntReg_T_2 = asSInt(_cntReg_T_1) @[Counter.scala 147:20]
    node _T = bits(cntReg, 7, 7) @[Counter.scala 148:14]
    node _GEN_0 = mux(_T, asSInt(UInt<8>("h6")), _cntReg_T_2) @[Counter.scala 147:10 148:19 149:12]
    node _GEN_1 = mux(_T, UInt<1>("h1"), UInt<1>("h0")) @[Counter.scala 145:11 148:19 150:13]
    node _io_cnt_T = asUInt(cntReg) @[Counter.scala 154:20]
    io_cnt <= _io_cnt_T @[Counter.scala 154:10]
    io_tick <= _GEN_1
    cntReg <= mux(reset1, asSInt(UInt<8>("h6")), _GEN_0) @[Counter.scala 144:{23,23}]
