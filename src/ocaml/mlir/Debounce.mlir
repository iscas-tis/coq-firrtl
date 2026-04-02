// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @Debounce(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %io_btnU: !firrtl.uint<1>, out %io_led: !firrtl.uint<8>) attributes {convention = #firrtl<convention scalarized>} {
  %io_btnU_0 = firrtl.wire {name = "io_btnU"} : !firrtl.uint<1>
  %io_led_1 = firrtl.wire {name = "io_led"} : !firrtl.uint<8>
  firrtl.strictconnect %io_btnU_0, %io_btnU : !firrtl.uint<1>
  firrtl.strictconnect %io_led, %io_led_1 : !firrtl.uint<8>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %btnSync_REG = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
  firrtl.strictconnect %btnSync_REG, %io_btnU_0 : !firrtl.uint<1>
  %btnSync = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
  firrtl.strictconnect %btnSync, %btnSync_REG : !firrtl.uint<1>
  %btnDebReg = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
  %c0_ui32 = firrtl.constant 0 : !firrtl.uint<32>
  %cntReg = firrtl.regreset %clock, %reset, %c0_ui32 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %c999999_ui20 = firrtl.constant 999999 : !firrtl.uint<20>
  %0 = firrtl.eq %cntReg, %c999999_ui20 : (!firrtl.uint<32>, !firrtl.uint<20>) -> !firrtl.uint<1>
  %tick = firrtl.node %0 : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %1 = firrtl.add %cntReg, %c1_ui1 : (!firrtl.uint<32>, !firrtl.uint<1>) -> !firrtl.uint<33>
  %_cntReg_T = firrtl.node %1 : !firrtl.uint<33>
  %2 = firrtl.tail %_cntReg_T, 1 : (!firrtl.uint<33>) -> !firrtl.uint<32>
  %_cntReg_T_1 = firrtl.node %2 : !firrtl.uint<32>
  %3 = firrtl.pad %c0_ui1, 32 : (!firrtl.uint<1>) -> !firrtl.uint<32>
  %4 = firrtl.mux(%tick, %3, %_cntReg_T_1) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %cntReg, %4 : !firrtl.uint<32>, !firrtl.uint<32>
  %5 = firrtl.mux(%tick, %btnSync, %btnDebReg) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.connect %btnDebReg, %5 : !firrtl.uint<1>, !firrtl.uint<1>
  %c0_ui3 = firrtl.constant 0 : !firrtl.uint<3>
  %shiftReg = firrtl.regreset %clock, %reset, %c0_ui3 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>
  %6 = firrtl.bits %shiftReg 1 to 0 : (!firrtl.uint<3>) -> !firrtl.uint<2>
  %_shiftReg_T = firrtl.node %6 : !firrtl.uint<2>
  %7 = firrtl.cat %_shiftReg_T, %btnDebReg : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<3>
  %_shiftReg_T_1 = firrtl.node %7 : !firrtl.uint<3>
  %8 = firrtl.mux(%tick, %_shiftReg_T_1, %shiftReg) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  firrtl.connect %shiftReg, %8 : !firrtl.uint<3>, !firrtl.uint<3>
  %9 = firrtl.bits %shiftReg 2 to 2 : (!firrtl.uint<3>) -> !firrtl.uint<1>
  %_btnClean_T = firrtl.node %9 : !firrtl.uint<1>
  %10 = firrtl.bits %shiftReg 1 to 1 : (!firrtl.uint<3>) -> !firrtl.uint<1>
  %_btnClean_T_1 = firrtl.node %10 : !firrtl.uint<1>
  %11 = firrtl.and %_btnClean_T, %_btnClean_T_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_btnClean_T_2 = firrtl.node %11 : !firrtl.uint<1>
  %_btnClean_T_3 = firrtl.node %9 : !firrtl.uint<1>
  %12 = firrtl.bits %shiftReg 0 to 0 : (!firrtl.uint<3>) -> !firrtl.uint<1>
  %_btnClean_T_4 = firrtl.node %12 : !firrtl.uint<1>
  %13 = firrtl.and %_btnClean_T_3, %_btnClean_T_4 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_btnClean_T_5 = firrtl.node %13 : !firrtl.uint<1>
  %14 = firrtl.or %_btnClean_T_2, %_btnClean_T_5 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_btnClean_T_6 = firrtl.node %14 : !firrtl.uint<1>
  %_btnClean_T_7 = firrtl.node %10 : !firrtl.uint<1>
  %_btnClean_T_8 = firrtl.node %12 : !firrtl.uint<1>
  %15 = firrtl.and %_btnClean_T_7, %_btnClean_T_8 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_btnClean_T_9 = firrtl.node %15 : !firrtl.uint<1>
  %16 = firrtl.or %_btnClean_T_6, %_btnClean_T_9 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %btnClean = firrtl.node %16 : !firrtl.uint<1>
  %risingEdge_REG = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
  firrtl.strictconnect %risingEdge_REG, %btnClean : !firrtl.uint<1>
  %17 = firrtl.eq %risingEdge_REG, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_risingEdge_T = firrtl.node %17 : !firrtl.uint<1>
  %18 = firrtl.and %btnClean, %_risingEdge_T : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %risingEdge = firrtl.node %18 : !firrtl.uint<1>
  %c0_ui8 = firrtl.constant 0 : !firrtl.uint<8>
  %reg = firrtl.regreset %clock, %reset, %c0_ui8 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>
  %19 = firrtl.add %reg, %c1_ui1 : (!firrtl.uint<8>, !firrtl.uint<1>) -> !firrtl.uint<9>
  %_reg_T = firrtl.node %19 : !firrtl.uint<9>
  %20 = firrtl.tail %_reg_T, 1 : (!firrtl.uint<9>) -> !firrtl.uint<8>
  %_reg_T_1 = firrtl.node %20 : !firrtl.uint<8>
  %21 = firrtl.mux(%risingEdge, %_reg_T_1, %reg) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  firrtl.connect %reg, %21 : !firrtl.uint<8>, !firrtl.uint<8>
  firrtl.strictconnect %io_led_1, %reg : !firrtl.uint<8>
}

