// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @DownTicker(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io_tick: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_tick_0 = firrtl.wire {name = "io_tick"} : !firrtl.uint<1>
  firrtl.strictconnect %io_tick, %io_tick_0 : !firrtl.uint<1>
  %c9_ui4 = firrtl.constant 9 : !firrtl.uint<4>
  %cntReg = firrtl.regreset %clock, %reset1, %c9_ui4 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %0 = firrtl.sub %cntReg, %c1_ui1 : (!firrtl.uint<4>, !firrtl.uint<1>) -> !firrtl.uint<5>
  %_cntReg_T = firrtl.node %0 : !firrtl.uint<5>
  %1 = firrtl.tail %_cntReg_T, 1 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_cntReg_T_1 = firrtl.node %1 : !firrtl.uint<4>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %2 = firrtl.eq %cntReg, %c0_ui1 : (!firrtl.uint<4>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %3 = firrtl.node %2 : !firrtl.uint<1>
  %4 = firrtl.mux(%3, %c9_ui4, %_cntReg_T_1) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  firrtl.connect %cntReg, %4 : !firrtl.uint<4>, !firrtl.uint<4>
  %5 = firrtl.eq %cntReg, %c9_ui4 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<1>
  %_io_tick_T = firrtl.node %5 : !firrtl.uint<1>
  firrtl.strictconnect %io_tick_0, %_io_tick_T : !firrtl.uint<1>
}

