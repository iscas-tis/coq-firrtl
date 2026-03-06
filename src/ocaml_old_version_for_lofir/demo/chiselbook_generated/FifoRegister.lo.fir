circuit FifoRegister :
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
