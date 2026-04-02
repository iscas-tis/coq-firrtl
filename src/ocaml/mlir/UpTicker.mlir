// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @UpTicker(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io_tick: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_tick_0 = firrtl.wire {name = "io_tick"} : !firrtl.uint<1>
  firrtl.strictconnect %io_tick, %io_tick_0 : !firrtl.uint<1>
  %c0_ui8 = firrtl.constant 0 : !firrtl.uint<8>
  %cntReg = firrtl.regreset %clock, %reset1, %c0_ui8 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %0 = firrtl.add %cntReg, %c1_ui1 : (!firrtl.uint<8>, !firrtl.uint<1>) -> !firrtl.uint<9>
  %_cntReg_T = firrtl.node %0 : !firrtl.uint<9>
  %1 = firrtl.tail %_cntReg_T, 1 : (!firrtl.uint<9>) -> !firrtl.uint<8>
  %_cntReg_T_1 = firrtl.node %1 : !firrtl.uint<8>
  %c9_ui4 = firrtl.constant 9 : !firrtl.uint<4>
  %2 = firrtl.eq %cntReg, %c9_ui4 : (!firrtl.uint<8>, !firrtl.uint<4>) -> !firrtl.uint<1>
  %tick = firrtl.node %2 : !firrtl.uint<1>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %3 = firrtl.pad %c0_ui1, 8 : (!firrtl.uint<1>) -> !firrtl.uint<8>
  %4 = firrtl.mux(%tick, %3, %_cntReg_T_1) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  firrtl.connect %cntReg, %4 : !firrtl.uint<8>, !firrtl.uint<8>
  firrtl.strictconnect %io_tick_0, %tick : !firrtl.uint<1>
}

