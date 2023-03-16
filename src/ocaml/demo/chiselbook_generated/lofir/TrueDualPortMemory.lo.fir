circuit TrueDualPortMemory :
  module TrueDualPortMemory :
    input clock : Clock
    input reset1 : UInt<1>
    input io_addrA : UInt<10>
    output io_rdDataA : UInt<8>
    input io_wrEnaA : UInt<1>
    input io_wrDataA : UInt<8>
    input io_addrB : UInt<10>
    output io_rdDataB : UInt<8>
    input io_wrEnaB : UInt<1>
    input io_wrDataB : UInt<8>

    mem mem1 : @[memory.scala 81:24]
      data-type => UInt<8>
      depth => 1024
      read-latency => 1
      write-latency => 1
      reader => io_rdDataA_MPORT
      reader => io_rdDataB_MPORT
      writer => MPORT
      writer => MPORT_1
      read-under-write => undefined
    node _GEN_0 = validif(UInt<1>("h1"), io_addrA) @[memory.scala 83:{25,25}]
    node _io_rdDataA_WIRE = _GEN_0 @[memory.scala 83:25]
    node _io_rdDataA_T = or(_io_rdDataA_WIRE, UInt<10>("h0")) @[memory.scala 83:25]
    node _io_rdDataA_T_1 = bits(_io_rdDataA_T, 9, 0) @[memory.scala 83:25]
    node _GEN_1 = mux(UInt<1>("h1"), UInt<1>("h1"), UInt<1>("h0")) @[memory.scala 81:24 83:{25,25}]
    node _GEN_2 = validif(UInt<1>("h1"), _io_rdDataA_T_1) @[memory.scala 83:{25,25}]
    node _GEN_3 = validif(UInt<1>("h1"), clock) @[memory.scala 83:{25,25}]
    node _GEN_4 = validif(io_wrEnaA, io_addrA) @[memory.scala 84:19]
    node _GEN_5 = validif(io_wrEnaA, clock) @[memory.scala 84:19]
    node _GEN_6 = mux(io_wrEnaA, UInt<1>("h1"), UInt<1>("h0")) @[memory.scala 84:19 81:24]
    node _GEN_7 = validif(io_wrEnaA, UInt<1>("h1")) @[memory.scala 84:19]
    node _GEN_8 = validif(io_wrEnaA, io_wrDataA) @[memory.scala 84:19]
    node _GEN_9 = validif(UInt<1>("h1"), io_addrB) @[memory.scala 87:{25,25}]
    node _io_rdDataB_WIRE = _GEN_9 @[memory.scala 87:25]
    node _io_rdDataB_T = or(_io_rdDataB_WIRE, UInt<10>("h0")) @[memory.scala 87:25]
    node _io_rdDataB_T_1 = bits(_io_rdDataB_T, 9, 0) @[memory.scala 87:25]
    node _GEN_10 = validif(UInt<1>("h1"), _io_rdDataB_T_1) @[memory.scala 87:{25,25}]
    node _GEN_11 = validif(io_wrEnaB, io_addrB) @[memory.scala 88:19]
    node _GEN_12 = validif(io_wrEnaB, clock) @[memory.scala 88:19]
    node _GEN_13 = mux(io_wrEnaB, UInt<1>("h1"), UInt<1>("h0")) @[memory.scala 88:19 81:24]
    node _GEN_14 = validif(io_wrEnaB, UInt<1>("h1")) @[memory.scala 88:19]
    node _GEN_15 = validif(io_wrEnaB, io_wrDataB) @[memory.scala 88:19]
    io_rdDataA <= mem1.io_rdDataA_MPORT.data @[memory.scala 83:14]
    io_rdDataB <= mem1.io_rdDataB_MPORT.data @[memory.scala 87:14]
    mem1.io_rdDataA_MPORT.addr <= _GEN_2
    mem1.io_rdDataA_MPORT.en <= _GEN_1
    mem1.io_rdDataA_MPORT.clk <= _GEN_3
    mem1.io_rdDataB_MPORT.addr <= _GEN_10
    mem1.io_rdDataB_MPORT.en <= _GEN_1
    mem1.io_rdDataB_MPORT.clk <= _GEN_3
    mem1.MPORT.addr <= _GEN_4
    mem1.MPORT.en <= _GEN_6
    mem1.MPORT.clk <= _GEN_5
    mem1.MPORT.data <= _GEN_8
    mem1.MPORT.mask <= _GEN_7
    mem1.MPORT_1.addr <= _GEN_11
    mem1.MPORT_1.en <= _GEN_13
    mem1.MPORT_1.clk <= _GEN_12
    mem1.MPORT_1.data <= _GEN_15
    mem1.MPORT_1.mask <= _GEN_14
