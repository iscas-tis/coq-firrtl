circuit MuxCounter :
  module MuxCounter :
    input clock : Clock
    input reset : UInt<1>
    output io : { cnt : UInt<8>, tick : UInt<1>}

    reg cntReg : UInt<8>, clock with :
      reset => (reset, UInt<8>("h0")) @[Counter.scala 65:23]
    node _cntReg_T = eq(cntReg, UInt<3>("h7")) @[Counter.scala 67:24]
    node _cntReg_T_1 = add(cntReg, UInt<1>("h1")) @[Counter.scala 67:43]
    node _cntReg_T_2 = tail(_cntReg_T_1, 1) @[Counter.scala 67:43]
    node _cntReg_T_3 = mux(_cntReg_T, UInt<1>("h0"), _cntReg_T_2) @[Counter.scala 67:16]
    cntReg <= _cntReg_T_3 @[Counter.scala 67:10]
    node _io_tick_T = eq(cntReg, UInt<3>("h7")) @[Counter.scala 70:21]
    io.tick <= _io_tick_T @[Counter.scala 70:11]
    io.cnt <= cntReg @[Counter.scala 71:10]

