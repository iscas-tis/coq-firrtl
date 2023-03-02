circuit InitMemory :
  module InitMemory :
    input clock : Clock
    input reset : UInt<1>
    output io : { flip rdAddr : UInt<10>, rdData : UInt<8>, flip wrAddr : UInt<10>, flip wrData : UInt<8>, flip wrEna : UInt<1>}

    smem mem : UInt<8> [1024] @[memory.scala 114:24]
    wire _io_rdData_WIRE : UInt @[memory.scala 119:24]
    _io_rdData_WIRE is invalid @[memory.scala 119:24]
    when UInt<1>("h1") : @[memory.scala 119:24]
      _io_rdData_WIRE <= io.rdAddr @[memory.scala 119:24]
      node _io_rdData_T = or(_io_rdData_WIRE, UInt<10>("h0")) @[memory.scala 119:24]
      node _io_rdData_T_1 = bits(_io_rdData_T, 9, 0) @[memory.scala 119:24]
      read mport io_rdData_MPORT = mem[_io_rdData_T_1], clock @[memory.scala 119:24]
    io.rdData <= io_rdData_MPORT @[memory.scala 119:13]
    when io.wrEna : @[memory.scala 122:18]
      write mport MPORT = mem[io.wrAddr], clock
      MPORT <= io.wrData


