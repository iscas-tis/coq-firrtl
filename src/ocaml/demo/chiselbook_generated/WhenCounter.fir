circuit WhenCounter :
  module WhenCounter :
    input clock : Clock
    input reset : UInt<1>
    output io : { cnt : UInt<8>, tick : UInt<1>}

    reg cntReg : UInt<8>, clock with :
      reset => (reset, UInt<8>("h0")) @[Counter.scala 38:23]
    node _cntReg_T = add(cntReg, UInt<1>("h1")) @[Counter.scala 40:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Counter.scala 40:20]
    cntReg <= _cntReg_T_1 @[Counter.scala 40:10]
    node _T = eq(cntReg, UInt<3>("h7")) @[Counter.scala 41:15]
    when _T : @[Counter.scala 41:22]
      cntReg <= UInt<1>("h0") @[Counter.scala 42:12]
    node _io_tick_T = eq(cntReg, UInt<3>("h7")) @[Counter.scala 46:21]
    io.tick <= _io_tick_T @[Counter.scala 46:11]
    io.cnt <= cntReg @[Counter.scala 47:10]

