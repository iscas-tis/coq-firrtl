// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @FifoRegister(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_enq_write: !firrtl.uint<1>, out %io_enq_full: !firrtl.uint<1>, in %io_enq_din: !firrtl.uint<10>, in %io_deq_read: !firrtl.uint<1>, out %io_deq_empty: !firrtl.uint<1>, out %io_deq_dout: !firrtl.uint<10>) attributes {convention = #firrtl<convention scalarized>} {
  %io_enq_write_0 = firrtl.wire {name = "io_enq_write"} : !firrtl.uint<1>
  %io_enq_full_1 = firrtl.wire {name = "io_enq_full"} : !firrtl.uint<1>
  %io_enq_din_2 = firrtl.wire {name = "io_enq_din"} : !firrtl.uint<10>
  %io_deq_read_3 = firrtl.wire {name = "io_deq_read"} : !firrtl.uint<1>
  %io_deq_empty_4 = firrtl.wire {name = "io_deq_empty"} : !firrtl.uint<1>
  %io_deq_dout_5 = firrtl.wire {name = "io_deq_dout"} : !firrtl.uint<10>
  firrtl.strictconnect %io_enq_write_0, %io_enq_write : !firrtl.uint<1>
  firrtl.strictconnect %io_enq_full, %io_enq_full_1 : !firrtl.uint<1>
  firrtl.strictconnect %io_enq_din_2, %io_enq_din : !firrtl.uint<10>
  firrtl.strictconnect %io_deq_read_3, %io_deq_read : !firrtl.uint<1>
  firrtl.strictconnect %io_deq_empty, %io_deq_empty_4 : !firrtl.uint<1>
  firrtl.strictconnect %io_deq_dout, %io_deq_dout_5 : !firrtl.uint<10>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %stateReg = firrtl.regreset %clock, %reset1, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>
  %c0_ui10 = firrtl.constant 0 : !firrtl.uint<10>
  %dataReg = firrtl.regreset %clock, %reset1, %c0_ui10 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<10>, !firrtl.uint<10>
  %0 = firrtl.eq %stateReg, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %1 = firrtl.node %0 : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %2 = firrtl.and %1, %io_enq_write_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %3 = firrtl.mux(%io_enq_write_0, %c1_ui1, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %4 = firrtl.mux(%io_enq_write_0, %io_enq_din_2, %dataReg) : (!firrtl.uint<1>, !firrtl.uint<10>, !firrtl.uint<10>) -> !firrtl.uint<10>
  %5 = firrtl.not %1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %6 = firrtl.eq %stateReg, %c1_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %7 = firrtl.node %6 : !firrtl.uint<1>
  %8 = firrtl.and %5, %7 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %9 = firrtl.and %8, %io_deq_read_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %10 = firrtl.mux(%io_deq_read_3, %c0_ui1, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %11 = firrtl.mux(%7, %10, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %12 = firrtl.mux(%1, %3, %11) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.connect %stateReg, %12 : !firrtl.uint<1>, !firrtl.uint<1>
  %13 = firrtl.pad %c0_ui1, 10 : (!firrtl.uint<1>) -> !firrtl.uint<10>
  %14 = firrtl.mux(%io_deq_read_3, %13, %dataReg) : (!firrtl.uint<1>, !firrtl.uint<10>, !firrtl.uint<10>) -> !firrtl.uint<10>
  %15 = firrtl.mux(%7, %14, %dataReg) : (!firrtl.uint<1>, !firrtl.uint<10>, !firrtl.uint<10>) -> !firrtl.uint<10>
  %16 = firrtl.mux(%1, %4, %15) : (!firrtl.uint<1>, !firrtl.uint<10>, !firrtl.uint<10>) -> !firrtl.uint<10>
  firrtl.connect %dataReg, %16 : !firrtl.uint<10>, !firrtl.uint<10>
  %17 = firrtl.not %7 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %18 = firrtl.and %5, %17 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %19 = firrtl.eq %stateReg, %c1_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_enq_full_T = firrtl.node %19 : !firrtl.uint<1>
  firrtl.strictconnect %io_enq_full_1, %_io_enq_full_T : !firrtl.uint<1>
  %_io_deq_empty_T = firrtl.node %0 : !firrtl.uint<1>
  firrtl.strictconnect %io_deq_empty_4, %_io_deq_empty_T : !firrtl.uint<1>
  firrtl.strictconnect %io_deq_dout_5, %dataReg : !firrtl.uint<10>
}

