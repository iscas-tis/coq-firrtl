circuit InitMemory :
  module InitMemory :
    input clock : Clock
    input reset1 : UInt<1>
    input io_rdAddr : UInt<10>
    output io_rdData : UInt<8>
    input io_wrAddr : UInt<10>
    input io_wrData : UInt<8>
    input io_wrEna : UInt<1>

    mem mem1 : @[memory.scala 114:24]
      data-type => UInt<8>
      depth => 1024
      read-latency => 0
      write-latency => 1
      reader => io_rdData_MPORT
      writer => MPORT
      read-under-write => old
    node _GEN_0 = validif(UInt<1>("h1"), io_rdAddr) @[memory.scala 119:{24,24}]
    node _io_rdData_WIRE = _GEN_0 @[memory.scala 119:24]
    node _io_rdData_T = or(_io_rdData_WIRE, UInt<10>("h0")) @[memory.scala 119:24]
    node _io_rdData_T_1 = bits(_io_rdData_T, 9, 0) @[memory.scala 119:24]
    node _GEN_1 = mux(UInt<1>("h1"), UInt<1>("h1"), UInt<1>("h0")) @[memory.scala 114:24 119:{24,24}]
    node _GEN_2 = validif(UInt<1>("h1"), _io_rdData_T_1) @[memory.scala 119:{24,24}]
    node _GEN_3 = validif(UInt<1>("h1"), clock) @[memory.scala 119:{24,24}]
    node _GEN_4 = validif(io_wrEna, io_wrAddr) @[memory.scala 122:18]
    node _GEN_5 = validif(io_wrEna, clock) @[memory.scala 122:18]
    node _GEN_6 = mux(io_wrEna, UInt<1>("h1"), UInt<1>("h0")) @[memory.scala 122:18 114:24]
    node _GEN_7 = validif(io_wrEna, UInt<1>("h1")) @[memory.scala 122:18]
    node _GEN_8 = validif(io_wrEna, io_wrData) @[memory.scala 122:18]
    io_rdData <= mem1.io_rdData_MPORT.data @[memory.scala 119:13]
    mem1.io_rdData_MPORT.addr <= _GEN_2
    mem1.io_rdData_MPORT.en <= _GEN_1
    mem1.io_rdData_MPORT.clk <= _GEN_3
    mem1.MPORT.addr <= _GEN_4
    mem1.MPORT.en <= _GEN_6
    mem1.MPORT.clk <= _GEN_5
    mem1.MPORT.data <= _GEN_8
    mem1.MPORT.mask <= _GEN_7
