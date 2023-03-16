circuit SequCounter :
  module SequCounter :
    input clock : Clock
    input reset : UInt<1>
    output io : { out : UInt<4>, flip event : UInt<1>, eventCnt : UInt<4>, tick : UInt<1>, lowCnt : UInt<4>}

    reg cntReg : UInt<4>, clock with :
      reset => (reset, UInt<4>("h0")) @[Sequential.scala 99:23]
    node _cntReg_T = add(cntReg, UInt<1>("h1")) @[Sequential.scala 101:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Sequential.scala 101:20]
    cntReg <= _cntReg_T_1 @[Sequential.scala 101:10]
    io.out <= cntReg @[Sequential.scala 103:10]
    reg cntEventsReg : UInt<4>, clock with :
      reset => (reset, UInt<4>("h0")) @[Sequential.scala 107:29]
    when io.event : @[Sequential.scala 108:15]
      node _cntEventsReg_T = add(cntEventsReg, UInt<1>("h1")) @[Sequential.scala 109:34]
      node _cntEventsReg_T_1 = tail(_cntEventsReg_T, 1) @[Sequential.scala 109:34]
      cntEventsReg <= _cntEventsReg_T_1 @[Sequential.scala 109:18]
    io.eventCnt <= cntEventsReg @[Sequential.scala 112:15]
    reg tickCounterReg : UInt<32>, clock with :
      reset => (reset, UInt<32>("h0")) @[Sequential.scala 116:31]
    node tick = eq(tickCounterReg, UInt<3>("h4")) @[Sequential.scala 117:29]
    node _tickCounterReg_T = add(tickCounterReg, UInt<1>("h1")) @[Sequential.scala 119:36]
    node _tickCounterReg_T_1 = tail(_tickCounterReg_T, 1) @[Sequential.scala 119:36]
    tickCounterReg <= _tickCounterReg_T_1 @[Sequential.scala 119:18]
    when tick : @[Sequential.scala 120:15]
      tickCounterReg <= UInt<1>("h0") @[Sequential.scala 121:20]
    reg lowFrequCntReg : UInt<4>, clock with :
      reset => (reset, UInt<4>("h0")) @[Sequential.scala 126:31]
    when tick : @[Sequential.scala 127:15]
      node _lowFrequCntReg_T = add(lowFrequCntReg, UInt<1>("h1")) @[Sequential.scala 128:38]
      node _lowFrequCntReg_T_1 = tail(_lowFrequCntReg_T, 1) @[Sequential.scala 128:38]
      lowFrequCntReg <= _lowFrequCntReg_T_1 @[Sequential.scala 128:20]
    io.tick <= tick @[Sequential.scala 132:11]
    io.lowCnt <= lowFrequCntReg @[Sequential.scala 133:13]

