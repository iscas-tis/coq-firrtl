circuit Count100 :
  module Count100 :
    input clock : Clock
    input reset1 : UInt<1>
    output io_cnt : UInt<8>

    reg cntReg : UInt<8>, clock with :
      reset => (UInt<1>("h0"), cntReg) @[Counter.scala 9:23]
    node _cntReg_T = eq(cntReg, UInt<4>("h9")) @[Counter.scala 11:24]
    node _cntReg_T_1 = add(cntReg, UInt<1>("h1")) @[Counter.scala 11:45]
    node _cntReg_T_2 = tail(_cntReg_T_1, 1) @[Counter.scala 11:45]
    node _cntReg_T_3 = mux(_cntReg_T, UInt<1>("h0"), _cntReg_T_2) @[Counter.scala 11:16]
    io_cnt <= cntReg @[Counter.scala 14:10]
    cntReg <= mux(reset1, UInt<8>("h0"), _cntReg_T_3) @[Counter.scala 11:10 9:{23,23}]
