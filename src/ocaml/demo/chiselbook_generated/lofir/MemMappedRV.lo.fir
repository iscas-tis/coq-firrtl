circuit MemMappedRV :
  module MemMappedRV :
    input clock : Clock
    input reset1 : UInt<1>
    input io_mem_address : UInt<4>
    input io_mem_rd : UInt<1>
    input io_mem_wr : UInt<1>
    output io_mem_rdData : UInt<32>
    input io_mem_wrData : UInt<32>
    output io_mem_ack : UInt<1>
    input io_tx_ready : UInt<1>
    output io_tx_valid : UInt<1>
    output io_tx_bits : UInt<8>
    output io_rx_ready : UInt<1>
    input io_rx_valid : UInt<1>
    input io_rx_bits : UInt<8>

    reg statusReg : UInt<2>, clock with :
      reset => (UInt<1>("h0"), statusReg) @[interconnect.scala 72:26]
    reg ackReg : UInt<1>, clock with :
      reset => (UInt<1>("h0"), ackReg) @[interconnect.scala 73:23]
    reg addrReg : UInt<1>, clock with :
      reset => (UInt<1>("h0"), addrReg) @[interconnect.scala 74:24]
    reg rdDlyReg : UInt<1>, clock with :
      reset => (UInt<1>("h0"), rdDlyReg) @[interconnect.scala 75:25]
    node _statusReg_T = cat(io_rx_valid, io_tx_ready) @[interconnect.scala 77:28]
    node _ackReg_T = or(io_mem_rd, io_mem_wr) @[interconnect.scala 80:23]
    node _GEN_0 = mux(io_mem_rd, io_mem_address, addrReg) @[interconnect.scala 84:20 85:13 74:24]
    node _T = eq(addrReg, UInt<1>("h1")) @[interconnect.scala 89:17]
    node _T_1 = and(_T, rdDlyReg) @[interconnect.scala 89:25]
    node _GEN_1 = mux(_T_1, UInt<1>("h1"), UInt<1>("h0")) @[interconnect.scala 88:15 89:38 90:17]
    node _io_mem_rdData_T = eq(addrReg, UInt<1>("h0")) @[interconnect.scala 92:32]
    node _io_mem_rdData_T_1 = mux(_io_mem_rdData_T, statusReg, io_rx_bits) @[interconnect.scala 92:23]
    io_mem_rdData <= pad(_io_mem_rdData_T_1, 32) @[interconnect.scala 92:17]
    io_mem_ack <= ackReg @[interconnect.scala 81:14]
    io_tx_valid <= io_mem_wr @[interconnect.scala 96:15]
    io_tx_bits <= bits(io_mem_wrData, 7, 0) @[interconnect.scala 95:14]
    io_rx_ready <= _GEN_1
    statusReg <= mux(reset1, UInt<2>("h0"), _statusReg_T) @[interconnect.scala 72:{26,26} 77:13]
    ackReg <= mux(reset1, UInt<1>("h0"), _ackReg_T) @[interconnect.scala 73:{23,23} 80:10]
    addrReg <= bits(mux(reset1, UInt<1>("h0"), _GEN_0), 0, 0) @[interconnect.scala 74:{24,24}]
    rdDlyReg <= mux(reset1, UInt<1>("h0"), io_mem_rd) @[interconnect.scala 75:{25,25} 87:12]
