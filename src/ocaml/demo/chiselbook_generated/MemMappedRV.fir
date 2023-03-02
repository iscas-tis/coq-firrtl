circuit MemMappedRV :
  module MemMappedRV :
    input clock : Clock
    input reset : UInt<1>
    output io : { mem : { flip address : UInt<4>, flip rd : UInt<1>, flip wr : UInt<1>, rdData : UInt<32>, flip wrData : UInt<32>, ack : UInt<1>}, tx : { flip ready : UInt<1>, valid : UInt<1>, bits : UInt<8>}, flip rx : { flip ready : UInt<1>, valid : UInt<1>, bits : UInt<8>}}

    reg statusReg : UInt<2>, clock with :
      reset => (reset, UInt<2>("h0")) @[interconnect.scala 72:26]
    reg ackReg : UInt<1>, clock with :
      reset => (reset, UInt<1>("h0")) @[interconnect.scala 73:23]
    reg addrReg : UInt<1>, clock with :
      reset => (reset, UInt<1>("h0")) @[interconnect.scala 74:24]
    reg rdDlyReg : UInt<1>, clock with :
      reset => (reset, UInt<1>("h0")) @[interconnect.scala 75:25]
    node _statusReg_T = cat(io.rx.valid, io.tx.ready) @[interconnect.scala 77:28]
    statusReg <= _statusReg_T @[interconnect.scala 77:13]
    node _ackReg_T = or(io.mem.rd, io.mem.wr) @[interconnect.scala 80:23]
    ackReg <= _ackReg_T @[interconnect.scala 80:10]
    io.mem.ack <= ackReg @[interconnect.scala 81:14]
    when io.mem.rd : @[interconnect.scala 84:20]
      addrReg <= io.mem.address @[interconnect.scala 85:13]
    rdDlyReg <= io.mem.rd @[interconnect.scala 87:12]
    io.rx.ready <= UInt<1>("h0") @[interconnect.scala 88:15]
    node _T = eq(addrReg, UInt<1>("h1")) @[interconnect.scala 89:17]
    node _T_1 = and(_T, rdDlyReg) @[interconnect.scala 89:25]
    when _T_1 : @[interconnect.scala 89:38]
      io.rx.ready <= UInt<1>("h1") @[interconnect.scala 90:17]
    node _io_mem_rdData_T = eq(addrReg, UInt<1>("h0")) @[interconnect.scala 92:32]
    node _io_mem_rdData_T_1 = mux(_io_mem_rdData_T, statusReg, io.rx.bits) @[interconnect.scala 92:23]
    io.mem.rdData <= _io_mem_rdData_T_1 @[interconnect.scala 92:17]
    io.tx.bits <= io.mem.wrData @[interconnect.scala 95:14]
    io.tx.valid <= io.mem.wr @[interconnect.scala 96:15]

