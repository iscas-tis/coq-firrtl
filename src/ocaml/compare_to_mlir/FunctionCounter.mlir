// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @FunctionCounter(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io_cnt: !firrtl.uint<8>, out %io_tick: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_cnt_0 = firrtl.wire {name = "io_cnt"} : !firrtl.uint<8>
  %io_tick_1 = firrtl.wire {name = "io_tick"} : !firrtl.uint<1>
  firrtl.strictconnect %io_cnt, %io_cnt_0 : !firrtl.uint<8>
  firrtl.strictconnect %io_tick, %io_tick_1 : !firrtl.uint<1>
  %c0_ui8 = firrtl.constant 0 : !firrtl.uint<8>
  %count10 = firrtl.regreset %clock, %reset1, %c0_ui8 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>
  %c10_ui4 = firrtl.constant 10 : !firrtl.uint<4>
  %0 = firrtl.eq %count10, %c10_ui4 : (!firrtl.uint<8>, !firrtl.uint<4>) -> !firrtl.uint<1>
  %_count10_cntReg_T = firrtl.node %0 : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %1 = firrtl.add %count10, %c1_ui1 : (!firrtl.uint<8>, !firrtl.uint<1>) -> !firrtl.uint<9>
  %_count10_cntReg_T_1 = firrtl.node %1 : !firrtl.uint<9>
  %2 = firrtl.tail %_count10_cntReg_T_1, 1 : (!firrtl.uint<9>) -> !firrtl.uint<8>
  %_count10_cntReg_T_2 = firrtl.node %2 : !firrtl.uint<8>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %3 = firrtl.mux(%_count10_cntReg_T, %c0_ui1, %_count10_cntReg_T_2) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %_count10_cntReg_T_3 = firrtl.node %3 : !firrtl.uint<8>
  firrtl.strictconnect %count10, %_count10_cntReg_T_3 : !firrtl.uint<8>
  %count99 = firrtl.regreset %clock, %reset1, %c0_ui8 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>
  %c99_ui7 = firrtl.constant 99 : !firrtl.uint<7>
  %4 = firrtl.eq %count99, %c99_ui7 : (!firrtl.uint<8>, !firrtl.uint<7>) -> !firrtl.uint<1>
  %_count99_cntReg_T = firrtl.node %4 : !firrtl.uint<1>
  %5 = firrtl.add %count99, %c1_ui1 : (!firrtl.uint<8>, !firrtl.uint<1>) -> !firrtl.uint<9>
  %_count99_cntReg_T_1 = firrtl.node %5 : !firrtl.uint<9>
  %6 = firrtl.tail %_count99_cntReg_T_1, 1 : (!firrtl.uint<9>) -> !firrtl.uint<8>
  %_count99_cntReg_T_2 = firrtl.node %6 : !firrtl.uint<8>
  %7 = firrtl.mux(%_count99_cntReg_T, %c0_ui1, %_count99_cntReg_T_2) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %_count99_cntReg_T_3 = firrtl.node %7 : !firrtl.uint<8>
  firrtl.strictconnect %count99, %_count99_cntReg_T_3 : !firrtl.uint<8>
  %testCounter = firrtl.regreset %clock, %reset1, %c0_ui8 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>
  %c9_ui4 = firrtl.constant 9 : !firrtl.uint<4>
  %8 = firrtl.eq %testCounter, %c9_ui4 : (!firrtl.uint<8>, !firrtl.uint<4>) -> !firrtl.uint<1>
  %_testCounter_cntReg_T = firrtl.node %8 : !firrtl.uint<1>
  %9 = firrtl.add %testCounter, %c1_ui1 : (!firrtl.uint<8>, !firrtl.uint<1>) -> !firrtl.uint<9>
  %_testCounter_cntReg_T_1 = firrtl.node %9 : !firrtl.uint<9>
  %10 = firrtl.tail %_testCounter_cntReg_T_1, 1 : (!firrtl.uint<9>) -> !firrtl.uint<8>
  %_testCounter_cntReg_T_2 = firrtl.node %10 : !firrtl.uint<8>
  %11 = firrtl.mux(%_testCounter_cntReg_T, %c0_ui1, %_testCounter_cntReg_T_2) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %_testCounter_cntReg_T_3 = firrtl.node %11 : !firrtl.uint<8>
  firrtl.strictconnect %testCounter, %_testCounter_cntReg_T_3 : !firrtl.uint<8>
  %_io_tick_T = firrtl.node %8 : !firrtl.uint<1>
  firrtl.strictconnect %io_tick_1, %_io_tick_T : !firrtl.uint<1>
  firrtl.strictconnect %io_cnt_0, %testCounter : !firrtl.uint<8>
}

