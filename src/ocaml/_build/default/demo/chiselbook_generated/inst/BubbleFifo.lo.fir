circuit BubbleFifo :
  module FifoRegister :
    input clock : Clock
    input reset1 : UInt<1>
    input io_enq_write : UInt<1>
    output io_enq_full : UInt<1>
    input io_enq_din : UInt<8>
    input io_deq_read : UInt<1>
    output io_deq_empty : UInt<1>
    output io_deq_dout : UInt<8>

    reg stateReg : UInt<1>, clock with :
      reset => (UInt<1>("h0"), stateReg) @[BubbleFifo.scala 62:25]
    reg dataReg : UInt<8>, clock with :
      reset => (UInt<1>("h0"), dataReg) @[BubbleFifo.scala 63:24]
    node _T = eq(stateReg, UInt<1>("h0")) @[BubbleFifo.scala 65:17]
    node _GEN_0 = mux(io_enq_write, UInt<1>("h1"), stateReg) @[BubbleFifo.scala 66:24 67:16 62:25]
    node _GEN_1 = mux(io_enq_write, io_enq_din, dataReg) @[BubbleFifo.scala 66:24 68:15 63:24]
    node _T_1 = eq(stateReg, UInt<1>("h1")) @[BubbleFifo.scala 70:23]
    node _GEN_2 = mux(io_deq_read, UInt<1>("h0"), stateReg) @[BubbleFifo.scala 71:23 72:16 62:25]
    node _GEN_3 = mux(io_deq_read, UInt<1>("h0"), dataReg) @[BubbleFifo.scala 71:23 73:15 63:24]
    node _GEN_4 = mux(_T_1, _GEN_2, stateReg) @[BubbleFifo.scala 62:25 70:33]
    node _GEN_5 = mux(_T_1, _GEN_3, dataReg) @[BubbleFifo.scala 63:24 70:33]
    node _GEN_6 = mux(_T, _GEN_0, _GEN_4) @[BubbleFifo.scala 65:28]
    node _GEN_7 = mux(_T, _GEN_1, _GEN_5) @[BubbleFifo.scala 65:28]
    node _io_enq_full_T = eq(stateReg, UInt<1>("h1")) @[BubbleFifo.scala 79:28]
    node _io_deq_empty_T = eq(stateReg, UInt<1>("h0")) @[BubbleFifo.scala 80:29]
    io_enq_full <= _io_enq_full_T @[BubbleFifo.scala 79:15]
    io_deq_empty <= _io_deq_empty_T @[BubbleFifo.scala 80:16]
    io_deq_dout <= dataReg @[BubbleFifo.scala 81:15]
    stateReg <= mux(reset1, UInt<1>("h0"), _GEN_6) @[BubbleFifo.scala 62:{25,25}]
    dataReg <= mux(reset1, UInt<8>("h0"), _GEN_7) @[BubbleFifo.scala 63:{24,24}]

  module BubbleFifo :
    input clock : Clock
    input reset1 : UInt<1>
    input io_enq_write : UInt<1>
    output io_enq_full : UInt<1>
    input io_enq_din : UInt<8>
    input io_deq_read : UInt<1>
    output io_deq_empty : UInt<1>
    output io_deq_dout : UInt<8>

    inst FifoRegister aof FifoRegister @[BubbleFifo.scala 105:43]
    inst FifoRegister_1 aof FifoRegister @[BubbleFifo.scala 105:43]
    inst FifoRegister_2 aof FifoRegister @[BubbleFifo.scala 105:43]
    inst FifoRegister_3 aof FifoRegister @[BubbleFifo.scala 105:43]
    inst FifoRegister_4 aof FifoRegister @[BubbleFifo.scala 105:43]
    inst FifoRegister_5 aof FifoRegister @[BubbleFifo.scala 105:43]
    inst FifoRegister_6 aof FifoRegister @[BubbleFifo.scala 105:43]
    inst FifoRegister_7 aof FifoRegister @[BubbleFifo.scala 105:43]
    node _T = not(FifoRegister.io_deq_empty) @[BubbleFifo.scala 108:36]
    node _T_1 = not(FifoRegister_1.io_enq_full) @[BubbleFifo.scala 109:31]
    node _T_2 = not(FifoRegister_1.io_deq_empty) @[BubbleFifo.scala 108:36]
    node _T_3 = not(FifoRegister_2.io_enq_full) @[BubbleFifo.scala 109:31]
    node _T_4 = not(FifoRegister_2.io_deq_empty) @[BubbleFifo.scala 108:36]
    node _T_5 = not(FifoRegister_3.io_enq_full) @[BubbleFifo.scala 109:31]
    node _T_6 = not(FifoRegister_3.io_deq_empty) @[BubbleFifo.scala 108:36]
    node _T_7 = not(FifoRegister_4.io_enq_full) @[BubbleFifo.scala 109:31]
    node _T_8 = not(FifoRegister_4.io_deq_empty) @[BubbleFifo.scala 108:36]
    node _T_9 = not(FifoRegister_5.io_enq_full) @[BubbleFifo.scala 109:31]
    node _T_10 = not(FifoRegister_5.io_deq_empty) @[BubbleFifo.scala 108:36]
    node _T_11 = not(FifoRegister_6.io_enq_full) @[BubbleFifo.scala 109:31]
    node _T_12 = not(FifoRegister_6.io_deq_empty) @[BubbleFifo.scala 108:36]
    node _T_13 = not(FifoRegister_7.io_enq_full) @[BubbleFifo.scala 109:31]
    io_enq_full <= FifoRegister.io_enq_full @[BubbleFifo.scala 111:10]
    io_deq_empty <= FifoRegister_7.io_deq_empty @[BubbleFifo.scala 112:10]
    io_deq_dout <= FifoRegister_7.io_deq_dout @[BubbleFifo.scala 112:10]
    FifoRegister.clock <= clock
    FifoRegister.reset1 <= reset1
    FifoRegister.io_enq_write <= io_enq_write @[BubbleFifo.scala 111:10]
    FifoRegister.io_enq_din <= io_enq_din @[BubbleFifo.scala 111:10]
    FifoRegister.io_deq_read <= _T_1 @[BubbleFifo.scala 109:28]
    FifoRegister_1.clock <= clock
    FifoRegister_1.reset1 <= reset1
    FifoRegister_1.io_enq_write <= _T @[BubbleFifo.scala 108:33]
    FifoRegister_1.io_enq_din <= FifoRegister.io_deq_dout @[BubbleFifo.scala 107:31]
    FifoRegister_1.io_deq_read <= _T_3 @[BubbleFifo.scala 109:28]
    FifoRegister_2.clock <= clock
    FifoRegister_2.reset1 <= reset1
    FifoRegister_2.io_enq_write <= _T_2 @[BubbleFifo.scala 108:33]
    FifoRegister_2.io_enq_din <= FifoRegister_1.io_deq_dout @[BubbleFifo.scala 107:31]
    FifoRegister_2.io_deq_read <= _T_5 @[BubbleFifo.scala 109:28]
    FifoRegister_3.clock <= clock
    FifoRegister_3.reset1 <= reset1
    FifoRegister_3.io_enq_write <= _T_4 @[BubbleFifo.scala 108:33]
    FifoRegister_3.io_enq_din <= FifoRegister_2.io_deq_dout @[BubbleFifo.scala 107:31]
    FifoRegister_3.io_deq_read <= _T_7 @[BubbleFifo.scala 109:28]
    FifoRegister_4.clock <= clock
    FifoRegister_4.reset1 <= reset1
    FifoRegister_4.io_enq_write <= _T_6 @[BubbleFifo.scala 108:33]
    FifoRegister_4.io_enq_din <= FifoRegister_3.io_deq_dout @[BubbleFifo.scala 107:31]
    FifoRegister_4.io_deq_read <= _T_9 @[BubbleFifo.scala 109:28]
    FifoRegister_5.clock <= clock
    FifoRegister_5.reset1 <= reset1
    FifoRegister_5.io_enq_write <= _T_8 @[BubbleFifo.scala 108:33]
    FifoRegister_5.io_enq_din <= FifoRegister_4.io_deq_dout @[BubbleFifo.scala 107:31]
    FifoRegister_5.io_deq_read <= _T_11 @[BubbleFifo.scala 109:28]
    FifoRegister_6.clock <= clock
    FifoRegister_6.reset1 <= reset1
    FifoRegister_6.io_enq_write <= _T_10 @[BubbleFifo.scala 108:33]
    FifoRegister_6.io_enq_din <= FifoRegister_5.io_deq_dout @[BubbleFifo.scala 107:31]
    FifoRegister_6.io_deq_read <= _T_13 @[BubbleFifo.scala 109:28]
    FifoRegister_7.clock <= clock
    FifoRegister_7.reset1 <= reset1
    FifoRegister_7.io_enq_write <= _T_12 @[BubbleFifo.scala 108:33]
    FifoRegister_7.io_enq_din <= FifoRegister_6.io_deq_dout @[BubbleFifo.scala 107:31]
    FifoRegister_7.io_deq_read <= io_deq_read @[BubbleFifo.scala 112:10]
