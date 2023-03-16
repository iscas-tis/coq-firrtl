circuit UseMemMappedRV :
  module MemMappedRV :
    input clock : Clock
    input reset : Reset
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

  module RegFifo :
    input clock : Clock
    input reset : Reset
    output io : { flip enq : { flip ready : UInt<1>, valid : UInt<1>, bits : UInt<8>}, deq : { flip ready : UInt<1>, valid : UInt<1>, bits : UInt<8>}}

    reg memReg : UInt<8>[3], clock with :
      reset => (UInt<1>("h0"), memReg) @[fifo.scala 131:19]
    wire incrRead : UInt<1> @[fifo.scala 133:29]
    incrRead <= UInt<1>("h0") @[fifo.scala 133:29]
    wire incrWrite : UInt<1> @[fifo.scala 134:30]
    incrWrite <= UInt<1>("h0") @[fifo.scala 134:30]
    reg readPtr : UInt<2>, clock with :
      reset => (reset, UInt<2>("h0")) @[fifo.scala 122:25]
    node _nextVal_T = eq(readPtr, UInt<2>("h2")) @[fifo.scala 123:30]
    node _nextVal_T_1 = add(readPtr, UInt<1>("h1")) @[fifo.scala 123:61]
    node _nextVal_T_2 = tail(_nextVal_T_1, 1) @[fifo.scala 123:61]
    node nextRead = mux(_nextVal_T, UInt<1>("h0"), _nextVal_T_2) @[fifo.scala 123:22]
    when incrRead : @[fifo.scala 124:16]
      readPtr <= nextRead @[fifo.scala 125:14]
    reg writePtr : UInt<2>, clock with :
      reset => (reset, UInt<2>("h0")) @[fifo.scala 122:25]
    node _nextVal_T_3 = eq(writePtr, UInt<2>("h2")) @[fifo.scala 123:30]
    node _nextVal_T_4 = add(writePtr, UInt<1>("h1")) @[fifo.scala 123:61]
    node _nextVal_T_5 = tail(_nextVal_T_4, 1) @[fifo.scala 123:61]
    node nextWrite = mux(_nextVal_T_3, UInt<1>("h0"), _nextVal_T_5) @[fifo.scala 123:22]
    when incrWrite : @[fifo.scala 124:16]
      writePtr <= nextWrite @[fifo.scala 125:14]
    reg emptyReg : UInt<1>, clock with :
      reset => (reset, UInt<1>("h1")) @[fifo.scala 138:25]
    reg fullReg : UInt<1>, clock with :
      reset => (reset, UInt<1>("h0")) @[fifo.scala 139:24]
    node op = cat(io.enq.valid, io.deq.ready) @[fifo.scala 141:25]
    wire doWrite : UInt<1> @[fifo.scala 142:28]
    doWrite <= UInt<1>("h0") @[fifo.scala 142:28]
    node _T = eq(UInt<1>("h0"), op) @[fifo.scala 144:14]
    when _T : @[fifo.scala 144:14]
      skip
    else :
      node _T_1 = eq(UInt<1>("h1"), op) @[fifo.scala 144:14]
      when _T_1 : @[fifo.scala 144:14]
        node _T_2 = eq(emptyReg, UInt<1>("h0")) @[fifo.scala 147:12]
        when _T_2 : @[fifo.scala 147:23]
          fullReg <= UInt<1>("h0") @[fifo.scala 148:17]
          node _emptyReg_T = eq(nextRead, writePtr) @[fifo.scala 149:30]
          emptyReg <= _emptyReg_T @[fifo.scala 149:18]
          incrRead <= UInt<1>("h1") @[fifo.scala 150:18]
      else :
        node _T_3 = eq(UInt<2>("h2"), op) @[fifo.scala 144:14]
        when _T_3 : @[fifo.scala 144:14]
          node _T_4 = eq(fullReg, UInt<1>("h0")) @[fifo.scala 154:12]
          when _T_4 : @[fifo.scala 154:22]
            doWrite <= UInt<1>("h1") @[fifo.scala 155:17]
            emptyReg <= UInt<1>("h0") @[fifo.scala 156:18]
            node _fullReg_T = eq(nextWrite, readPtr) @[fifo.scala 157:30]
            fullReg <= _fullReg_T @[fifo.scala 157:17]
            incrWrite <= UInt<1>("h1") @[fifo.scala 158:19]
        else :
          node _T_5 = eq(UInt<2>("h3"), op) @[fifo.scala 144:14]
          when _T_5 : @[fifo.scala 144:14]
            node _T_6 = eq(fullReg, UInt<1>("h0")) @[fifo.scala 162:12]
            when _T_6 : @[fifo.scala 162:22]
              doWrite <= UInt<1>("h1") @[fifo.scala 163:17]
              emptyReg <= UInt<1>("h0") @[fifo.scala 164:18]
              when emptyReg : @[fifo.scala 165:24]
                fullReg <= UInt<1>("h0") @[fifo.scala 166:19]
              else :
                node _fullReg_T_1 = eq(nextWrite, nextRead) @[fifo.scala 168:32]
                fullReg <= _fullReg_T_1 @[fifo.scala 168:19]
              incrWrite <= UInt<1>("h1") @[fifo.scala 170:19]
            node _T_7 = eq(emptyReg, UInt<1>("h0")) @[fifo.scala 172:12]
            when _T_7 : @[fifo.scala 172:23]
              fullReg <= UInt<1>("h0") @[fifo.scala 173:17]
              when fullReg : @[fifo.scala 174:23]
                emptyReg <= UInt<1>("h0") @[fifo.scala 175:20]
              else :
                node _emptyReg_T_1 = eq(nextRead, nextWrite) @[fifo.scala 177:32]
                emptyReg <= _emptyReg_T_1 @[fifo.scala 177:20]
              incrRead <= UInt<1>("h1") @[fifo.scala 179:18]
    when doWrite : @[fifo.scala 184:17]
      memReg[writePtr] <= io.enq.bits @[fifo.scala 185:22]
    io.deq.bits <= memReg[readPtr] @[fifo.scala 188:15]
    node _io_enq_ready_T = eq(fullReg, UInt<1>("h0")) @[fifo.scala 189:19]
    io.enq.ready <= _io_enq_ready_T @[fifo.scala 189:16]
    node _io_deq_valid_T = eq(emptyReg, UInt<1>("h0")) @[fifo.scala 190:19]
    io.deq.valid <= _io_deq_valid_T @[fifo.scala 190:16]

  module UseMemMappedRV :
    input clock : Clock
    input reset : UInt<1>
    output io : { mem : { flip address : UInt<4>, flip rd : UInt<1>, flip wr : UInt<1>, rdData : UInt<32>, flip wrData : UInt<32>, ack : UInt<1>}}

    inst memDevice of MemMappedRV @[interconnect.scala 113:25]
    memDevice.clock <= clock
    memDevice.reset <= reset
    inst fifo of RegFifo @[interconnect.scala 114:20]
    fifo.clock <= clock
    fifo.reset <= reset
    fifo.io.enq <= memDevice.io.tx @[interconnect.scala 115:19]
    memDevice.io.rx <= fifo.io.deq @[interconnect.scala 116:19]
    io.mem.ack <= memDevice.io.mem.ack @[interconnect.scala 117:10]
    memDevice.io.mem.wrData <= io.mem.wrData @[interconnect.scala 117:10]
    io.mem.rdData <= memDevice.io.mem.rdData @[interconnect.scala 117:10]
    memDevice.io.mem.wr <= io.mem.wr @[interconnect.scala 117:10]
    memDevice.io.mem.rd <= io.mem.rd @[interconnect.scala 117:10]
    memDevice.io.mem.address <= io.mem.address @[interconnect.scala 117:10]

