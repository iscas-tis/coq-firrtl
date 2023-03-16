circuit CounterDevice :
  module CounterDevice :
    input clock : Clock
    input reset : UInt<1>
    output io : { flip addr : UInt<2>, flip wr : UInt<1>, flip rd : UInt<1>, flip wrData : UInt<32>, rdData : UInt<32>, ack : UInt<1>}

    reg ackReg : UInt<1>, clock with :
      reset => (reset, UInt<1>("h0")) @[interconnect.scala 16:23]
    reg addrReg : UInt<2>, clock with :
      reset => (reset, UInt<2>("h0")) @[interconnect.scala 17:24]
    wire _cntRegs_WIRE : UInt<32>[4] @[interconnect.scala 18:32]
    _cntRegs_WIRE[0] <= UInt<32>("h0") @[interconnect.scala 18:32]
    _cntRegs_WIRE[1] <= UInt<32>("h0") @[interconnect.scala 18:32]
    _cntRegs_WIRE[2] <= UInt<32>("h0") @[interconnect.scala 18:32]
    _cntRegs_WIRE[3] <= UInt<32>("h0") @[interconnect.scala 18:32]
    reg cntRegs : UInt<32>[4], clock with :
      reset => (reset, _cntRegs_WIRE) @[interconnect.scala 18:24]
    node _ackReg_T = or(io.rd, io.wr) @[interconnect.scala 20:19]
    ackReg <= _ackReg_T @[interconnect.scala 20:10]
    when io.rd : @[interconnect.scala 21:15]
      addrReg <= io.addr @[interconnect.scala 22:13]
    io.rdData <= cntRegs[addrReg] @[interconnect.scala 24:13]
    node _cntRegs_0_T = add(cntRegs[0], UInt<1>("h1")) @[interconnect.scala 27:30]
    node _cntRegs_0_T_1 = tail(_cntRegs_0_T, 1) @[interconnect.scala 27:30]
    cntRegs[0] <= _cntRegs_0_T_1 @[interconnect.scala 27:16]
    node _cntRegs_1_T = add(cntRegs[1], UInt<1>("h1")) @[interconnect.scala 27:30]
    node _cntRegs_1_T_1 = tail(_cntRegs_1_T, 1) @[interconnect.scala 27:30]
    cntRegs[1] <= _cntRegs_1_T_1 @[interconnect.scala 27:16]
    node _cntRegs_2_T = add(cntRegs[2], UInt<1>("h1")) @[interconnect.scala 27:30]
    node _cntRegs_2_T_1 = tail(_cntRegs_2_T, 1) @[interconnect.scala 27:30]
    cntRegs[2] <= _cntRegs_2_T_1 @[interconnect.scala 27:16]
    node _cntRegs_3_T = add(cntRegs[3], UInt<1>("h1")) @[interconnect.scala 27:30]
    node _cntRegs_3_T_1 = tail(_cntRegs_3_T, 1) @[interconnect.scala 27:30]
    cntRegs[3] <= _cntRegs_3_T_1 @[interconnect.scala 27:16]
    when io.wr : @[interconnect.scala 29:16]
      cntRegs[io.addr] <= io.wrData @[interconnect.scala 30:22]
    io.ack <= ackReg @[interconnect.scala 33:10]

