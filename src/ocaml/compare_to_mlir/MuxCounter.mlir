// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @MuxCounter(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io_cnt: !firrtl.uint<8>, out %io_tick: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_cnt_0 = firrtl.wire {name = "io_cnt"} : !firrtl.uint<8>
  %io_tick_1 = firrtl.wire {name = "io_tick"} : !firrtl.uint<1>
  firrtl.strictconnect %io_cnt, %io_cnt_0 : !firrtl.uint<8>
  firrtl.strictconnect %io_tick, %io_tick_1 : !firrtl.uint<1>
  %c0_ui8 = firrtl.constant 0 : !firrtl.uint<8>
  %cntReg = firrtl.regreset %clock, %reset1, %c0_ui8 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>
  %c9_ui4 = firrtl.constant 9 : !firrtl.uint<4>
  %0 = firrtl.eq %cntReg, %c9_ui4 : (!firrtl.uint<8>, !firrtl.uint<4>) -> !firrtl.uint<1>
  %_cntReg_T = firrtl.node %0 : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %1 = firrtl.add %cntReg, %c1_ui1 : (!firrtl.uint<8>, !firrtl.uint<1>) -> !firrtl.uint<9>
  %_cntReg_T_1 = firrtl.node %1 : !firrtl.uint<9>
  %2 = firrtl.tail %_cntReg_T_1, 1 : (!firrtl.uint<9>) -> !firrtl.uint<8>
  %_cntReg_T_2 = firrtl.node %2 : !firrtl.uint<8>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %3 = firrtl.mux(%_cntReg_T, %c0_ui1, %_cntReg_T_2) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %_cntReg_T_3 = firrtl.node %3 : !firrtl.uint<8>
  firrtl.strictconnect %cntReg, %_cntReg_T_3 : !firrtl.uint<8>
  %_io_tick_T = firrtl.node %0 : !firrtl.uint<1>
  firrtl.strictconnect %io_tick_1, %_io_tick_T : !firrtl.uint<1>
  firrtl.strictconnect %io_cnt_0, %cntReg : !firrtl.uint<8>
}

