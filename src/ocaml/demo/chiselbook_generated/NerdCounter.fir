circuit NerdCounter :
  module NerdCounter :
    input clock : Clock
    input reset : UInt<1>
    output io : { cnt : UInt<8>, tick : UInt<1>}

    reg cntReg : SInt<8>, clock with :
      reset => (reset, asSInt(UInt<8>("h6"))) @[Counter.scala 144:23]
    io.tick <= UInt<1>("h0") @[Counter.scala 145:11]
    node _cntReg_T = sub(cntReg, asSInt(UInt<2>("h1"))) @[Counter.scala 147:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Counter.scala 147:20]
    node _cntReg_T_2 = asSInt(_cntReg_T_1) @[Counter.scala 147:20]
    cntReg <= _cntReg_T_2 @[Counter.scala 147:10]
    node _T = bits(cntReg, 7, 7) @[Counter.scala 148:14]
    when _T : @[Counter.scala 148:19]
      cntReg <= asSInt(UInt<8>("h6")) @[Counter.scala 149:12]
      io.tick <= UInt<1>("h1") @[Counter.scala 150:13]
    node _io_cnt_T = asUInt(cntReg) @[Counter.scala 154:20]
    io.cnt <= _io_cnt_T @[Counter.scala 154:10]

