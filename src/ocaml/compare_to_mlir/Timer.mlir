// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @Timer(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_din: !firrtl.uint<8>, in %io_load: !firrtl.uint<1>, out %io_done: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_din_0 = firrtl.wire {name = "io_din"} : !firrtl.uint<8>
  %io_load_1 = firrtl.wire {name = "io_load"} : !firrtl.uint<1>
  %io_done_2 = firrtl.wire {name = "io_done"} : !firrtl.uint<1>
  firrtl.strictconnect %io_din_0, %io_din : !firrtl.uint<8>
  firrtl.strictconnect %io_load_1, %io_load : !firrtl.uint<1>
  firrtl.strictconnect %io_done, %io_done_2 : !firrtl.uint<1>
  %c0_ui8 = firrtl.constant 0 : !firrtl.uint<8>
  %cntReg = firrtl.regreset %clock, %reset1, %c0_ui8 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %0 = firrtl.eq %cntReg, %c0_ui1 : (!firrtl.uint<8>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %done = firrtl.node %0 : !firrtl.uint<1>
  %next = firrtl.wire : !firrtl.uint<8>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %1 = firrtl.not %io_load_1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %2 = firrtl.eq %done, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %3 = firrtl.node %2 : !firrtl.uint<1>
  %4 = firrtl.and %1, %3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %5 = firrtl.sub %cntReg, %c1_ui1 : (!firrtl.uint<8>, !firrtl.uint<1>) -> !firrtl.uint<9>
  %_next_T = firrtl.node %5 : !firrtl.uint<9>
  %6 = firrtl.tail %_next_T, 1 : (!firrtl.uint<9>) -> !firrtl.uint<8>
  %_next_T_1 = firrtl.node %6 : !firrtl.uint<8>
  %7 = firrtl.mux(%3, %_next_T_1, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<1>) -> !firrtl.uint<8>
  %8 = firrtl.mux(%io_load_1, %io_din_0, %7) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  firrtl.connect %next, %8 : !firrtl.uint<8>, !firrtl.uint<8>
  firrtl.connect %cntReg, %next : !firrtl.uint<8>, !firrtl.uint<8>
  firrtl.strictconnect %io_done_2, %done : !firrtl.uint<1>
}

