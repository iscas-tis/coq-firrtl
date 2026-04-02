// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @NerdCounter(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io_cnt: !firrtl.uint<8>, out %io_tick: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_cnt_0 = firrtl.wire {name = "io_cnt"} : !firrtl.uint<8>
  %io_tick_1 = firrtl.wire {name = "io_tick"} : !firrtl.uint<1>
  firrtl.strictconnect %io_cnt, %io_cnt_0 : !firrtl.uint<8>
  firrtl.strictconnect %io_tick, %io_tick_1 : !firrtl.uint<1>
  %c8_ui8 = firrtl.constant 8 : !firrtl.uint<8>
  %0 = firrtl.asSInt %c8_ui8 : (!firrtl.uint<8>) -> !firrtl.sint<8>
  %cntReg = firrtl.regreset %clock, %reset1, %0 : !firrtl.clock, !firrtl.uint<1>, !firrtl.sint<8>, !firrtl.sint<8>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %c1_ui2 = firrtl.constant 1 : !firrtl.uint<2>
  %1 = firrtl.asSInt %c1_ui2 : (!firrtl.uint<2>) -> !firrtl.sint<2>
  %2 = firrtl.sub %cntReg, %1 : (!firrtl.sint<8>, !firrtl.sint<2>) -> !firrtl.sint<9>
  %_cntReg_T = firrtl.node %2 : !firrtl.sint<9>
  %3 = firrtl.tail %_cntReg_T, 1 : (!firrtl.sint<9>) -> !firrtl.uint<8>
  %_cntReg_T_1 = firrtl.node %3 : !firrtl.uint<8>
  %4 = firrtl.asSInt %_cntReg_T_1 : (!firrtl.uint<8>) -> !firrtl.sint<8>
  %_cntReg_T_2 = firrtl.node %4 : !firrtl.sint<8>
  %5 = firrtl.bits %cntReg 7 to 7 : (!firrtl.sint<8>) -> !firrtl.uint<1>
  %6 = firrtl.node %5 : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %7 = firrtl.mux(%6, %0, %_cntReg_T_2) : (!firrtl.uint<1>, !firrtl.sint<8>, !firrtl.sint<8>) -> !firrtl.sint<8>
  firrtl.connect %cntReg, %7 : !firrtl.sint<8>, !firrtl.sint<8>
  firrtl.connect %io_tick_1, %6 : !firrtl.uint<1>, !firrtl.uint<1>
  %8 = firrtl.asUInt %cntReg : (!firrtl.sint<8>) -> !firrtl.uint<8>
  %_io_cnt_T = firrtl.node %8 : !firrtl.uint<8>
  firrtl.strictconnect %io_cnt_0, %_io_cnt_T : !firrtl.uint<8>
}

