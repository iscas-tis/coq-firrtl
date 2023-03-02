circuit ForwardingMemory :
  module ForwardingMemory :
    input clock : Clock
    input reset : UInt<1>
    output io : { flip rdAddr : UInt<10>, rdData : UInt<8>, flip wrAddr : UInt<10>, flip wrData : UInt<8>, flip wrEna : UInt<1>}

    smem mem : UInt<8> [1024] @[memory.scala 43:24]
    reg wrDataReg : UInt, clock with :
      reset => (UInt<1>("h0"), wrDataReg) @[memory.scala 45:26]
    wrDataReg <= io.wrData @[memory.scala 45:26]
    node _doForwardReg_T = eq(io.wrAddr, io.rdAddr) @[memory.scala 46:40]
    node _doForwardReg_T_1 = and(_doForwardReg_T, io.wrEna) @[memory.scala 46:54]
    reg doForwardReg : UInt<1>, clock with :
      reset => (UInt<1>("h0"), doForwardReg) @[memory.scala 46:29]
    doForwardReg <= _doForwardReg_T_1 @[memory.scala 46:29]
    wire _memData_WIRE : UInt @[memory.scala 48:25]
    _memData_WIRE is invalid @[memory.scala 48:25]
    when UInt<1>("h1") : @[memory.scala 48:25]
      _memData_WIRE <= io.rdAddr @[memory.scala 48:25]
      node _memData_T = or(_memData_WIRE, UInt<10>("h0")) @[memory.scala 48:25]
      node _memData_T_1 = bits(_memData_T, 9, 0) @[memory.scala 48:25]
      read mport memData = mem[_memData_T_1], clock @[memory.scala 48:25]
    when io.wrEna : @[memory.scala 50:18]
      write mport MPORT = mem[io.wrAddr], clock
      MPORT <= io.wrData
    node _io_rdData_T = mux(doForwardReg, wrDataReg, memData) @[memory.scala 54:19]
    io.rdData <= _io_rdData_T @[memory.scala 54:13]

