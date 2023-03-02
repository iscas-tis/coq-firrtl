circuit ForwardingMemory :
  module ForwardingMemory :
    input clock : Clock
    input reset1 : UInt<1>
    input io_rdAddr : UInt<10>
    output io_rdData : UInt<8>
    input io_wrAddr : UInt<10>
    input io_wrData : UInt<8>
    input io_wrEna : UInt<1>

    mem mem1 : @[memory.scala 43:24]
      data-type => UInt<8>
      depth => 1024
      read-latency => 1
      write-latency => 1
      reader => memData
      writer => MPORT
      read-under-write => undefined
    reg wrDataReg : UInt<8>, clock with :
      reset => (UInt<1>("h0"), wrDataReg) @[memory.scala 45:26]
    node _doForwardReg_T = eq(io_wrAddr, io_rdAddr) @[memory.scala 46:40]
    node _doForwardReg_T_1 = and(_doForwardReg_T, io_wrEna) @[memory.scala 46:54]
    reg doForwardReg : UInt<1>, clock with :
      reset => (UInt<1>("h0"), doForwardReg) @[memory.scala 46:29]
    node _GEN_0 = validif(UInt<1>("h1"), io_rdAddr) @[memory.scala 48:{25,25}]
    node _memData_WIRE = _GEN_0 @[memory.scala 48:25]
    node _memData_T = or(_memData_WIRE, UInt<10>("h0")) @[memory.scala 48:25]
    node _memData_T_1 = bits(_memData_T, 9, 0) @[memory.scala 48:25]
    node _GEN_1 = mux(UInt<1>("h1"), UInt<1>("h1"), UInt<1>("h0")) @[memory.scala 43:24 48:{25,25}]
    node _GEN_2 = validif(UInt<1>("h1"), _memData_T_1) @[memory.scala 48:{25,25}]
    node _GEN_3 = validif(UInt<1>("h1"), clock) @[memory.scala 48:{25,25}]
    node _GEN_4 = validif(io_wrEna, io_wrAddr) @[memory.scala 50:18]
    node _GEN_5 = validif(io_wrEna, clock) @[memory.scala 50:18]
    node _GEN_6 = mux(io_wrEna, UInt<1>("h1"), UInt<1>("h0")) @[memory.scala 50:18 43:24]
    node _GEN_7 = validif(io_wrEna, UInt<1>("h1")) @[memory.scala 50:18]
    node _GEN_8 = validif(io_wrEna, io_wrData) @[memory.scala 50:18]
    node _io_rdData_T = mux(doForwardReg, wrDataReg, mem1.memData.data) @[memory.scala 54:19]
    io_rdData <= _io_rdData_T @[memory.scala 54:13]
    mem1.memData.addr <= _GEN_2
    mem1.memData.en <= _GEN_1
    mem1.memData.clk <= _GEN_3
    mem1.MPORT.addr <= _GEN_4
    mem1.MPORT.en <= _GEN_6
    mem1.MPORT.clk <= _GEN_5
    mem1.MPORT.data <= _GEN_8
    mem1.MPORT.mask <= _GEN_7
    wrDataReg <= io_wrData @[memory.scala 45:26]
    doForwardReg <= _doForwardReg_T_1 @[memory.scala 46:29]
