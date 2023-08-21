circuit SequCounter :
  module SequCounter :
    input clock : Clock
    input reset1 : UInt<1>
    output io_out : UInt<4>
    input io_event : UInt<1>
    output io_eventCnt : UInt<4>
    output io_tick : UInt<1>
    output io_lowCnt : UInt<4>

    reg cntReg : UInt<4>, clock with :
      reset => (UInt<1>("h0"), cntReg) @[Sequential.scala 99:23]
    node _cntReg_T = add(cntReg, UInt<1>("h1")) @[Sequential.scala 101:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Sequential.scala 101:20]
    reg cntEventsReg : UInt<4>, clock with :
      reset => (UInt<1>("h0"), cntEventsReg) @[Sequential.scala 107:29]
    node _cntEventsReg_T = add(cntEventsReg, UInt<1>("h1")) @[Sequential.scala 109:34]
    node _cntEventsReg_T_1 = tail(_cntEventsReg_T, 1) @[Sequential.scala 109:34]
    node _GEN_0 = mux(io_event, _cntEventsReg_T_1, cntEventsReg) @[Sequential.scala 108:15 109:18 107:29]
    reg tickCounterReg : UInt<32>, clock with :
      reset => (UInt<1>("h0"), tickCounterReg) @[Sequential.scala 116:31]
    node tick = eq(tickCounterReg, UInt<3>("h4")) @[Sequential.scala 117:29]
    node _tickCounterReg_T = add(tickCounterReg, UInt<1>("h1")) @[Sequential.scala 119:36]
    node _tickCounterReg_T_1 = tail(_tickCounterReg_T, 1) @[Sequential.scala 119:36]
    node _GEN_1 = mux(tick, UInt<1>("h0"), _tickCounterReg_T_1) @[Sequential.scala 120:15 119:18 121:20]
    reg lowFrequCntReg : UInt<4>, clock with :
      reset => (UInt<1>("h0"), lowFrequCntReg) @[Sequential.scala 126:31]
    node _lowFrequCntReg_T = add(lowFrequCntReg, UInt<1>("h1")) @[Sequential.scala 128:38]
    node _lowFrequCntReg_T_1 = tail(_lowFrequCntReg_T, 1) @[Sequential.scala 128:38]
    node _GEN_2 = mux(tick, _lowFrequCntReg_T_1, lowFrequCntReg) @[Sequential.scala 127:15 128:20 126:31]
    io_out <= cntReg @[Sequential.scala 103:10]
    io_eventCnt <= cntEventsReg @[Sequential.scala 112:15]
    io_tick <= tick @[Sequential.scala 132:11]
    io_lowCnt <= lowFrequCntReg @[Sequential.scala 133:13]
    cntReg <= mux(reset1, UInt<4>("h0"), _cntReg_T_1) @[Sequential.scala 101:10 99:{23,23}]
    cntEventsReg <= mux(reset1, UInt<4>("h0"), _GEN_0) @[Sequential.scala 107:{29,29}]
    tickCounterReg <= mux(reset1, UInt<32>("h0"), _GEN_1) @[Sequential.scala 116:{31,31}]
    lowFrequCntReg <= mux(reset1, UInt<4>("h0"), _GEN_2) @[Sequential.scala 126:{31,31}]
