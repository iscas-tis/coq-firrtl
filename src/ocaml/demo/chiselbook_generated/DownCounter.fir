circuit DownCounter :
  module DownCounter :
    input clock : Clock
    input reset : UInt<1>
    output io : { cnt : UInt<8>, tick : UInt<1>}

    reg cntReg : UInt, clock with :
      reset => (reset, UInt<3>("h7")) @[Counter.scala 88:23]
    node _cntReg_T = sub(cntReg, UInt<1>("h1")) @[Counter.scala 90:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Counter.scala 90:20]
    cntReg <= _cntReg_T_1 @[Counter.scala 90:10]
    node _T = eq(cntReg, UInt<1>("h0")) @[Counter.scala 91:15]
    when _T : @[Counter.scala 91:24]
      cntReg <= UInt<3>("h7") @[Counter.scala 92:12]
    node _io_tick_T = eq(cntReg, UInt<1>("h0")) @[Counter.scala 96:21]
    io.tick <= _io_tick_T @[Counter.scala 96:11]
    io.cnt <= cntReg @[Counter.scala 97:10]

