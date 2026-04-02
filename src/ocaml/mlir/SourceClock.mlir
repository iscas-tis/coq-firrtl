// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @SourceClock(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io_c_data: !firrtl.uint<32>, out %io_c_valid: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_c_data_0 = firrtl.wire {name = "io_c_data"} : !firrtl.uint<32>
  %io_c_valid_1 = firrtl.wire {name = "io_c_valid"} : !firrtl.uint<1>
  firrtl.strictconnect %io_c_data, %io_c_data_0 : !firrtl.uint<32>
  firrtl.strictconnect %io_c_valid, %io_c_valid_1 : !firrtl.uint<1>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %valid = firrtl.regreset %clock, %reset1, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>
  %c0_ui32 = firrtl.constant 0 : !firrtl.uint<32>
  %cntReg = firrtl.regreset %clock, %reset1, %c0_ui32 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %c0_ui2 = firrtl.constant 0 : !firrtl.uint<2>
  %xReg = firrtl.regreset %clock, %reset1, %c0_ui2 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %0 = firrtl.add %xReg, %c1_ui1 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<3>
  %_xReg_T = firrtl.node %0 : !firrtl.uint<3>
  %1 = firrtl.tail %_xReg_T, 1 : (!firrtl.uint<3>) -> !firrtl.uint<2>
  %_xReg_T_1 = firrtl.node %1 : !firrtl.uint<2>
  firrtl.strictconnect %xReg, %_xReg_T_1 : !firrtl.uint<2>
  %2 = firrtl.bits %xReg 1 to 1 : (!firrtl.uint<2>) -> !firrtl.uint<1>
  %_valid_T = firrtl.node %2 : !firrtl.uint<1>
  firrtl.strictconnect %valid, %_valid_T : !firrtl.uint<1>
  %3 = firrtl.eq %valid, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_falling_T = firrtl.node %3 : !firrtl.uint<1>
  %falling_REG = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
  firrtl.strictconnect %falling_REG, %valid : !firrtl.uint<1>
  %4 = firrtl.and %_falling_T, %falling_REG : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %falling = firrtl.node %4 : !firrtl.uint<1>
  %5 = firrtl.add %cntReg, %c1_ui1 : (!firrtl.uint<32>, !firrtl.uint<1>) -> !firrtl.uint<33>
  %_cntReg_T = firrtl.node %5 : !firrtl.uint<33>
  %6 = firrtl.tail %_cntReg_T, 1 : (!firrtl.uint<33>) -> !firrtl.uint<32>
  %_cntReg_T_1 = firrtl.node %6 : !firrtl.uint<32>
  %7 = firrtl.mux(%falling, %_cntReg_T_1, %cntReg) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %cntReg, %7 : !firrtl.uint<32>, !firrtl.uint<32>
  firrtl.strictconnect %io_c_valid_1, %valid : !firrtl.uint<1>
  firrtl.strictconnect %io_c_data_0, %cntReg : !firrtl.uint<32>
}

