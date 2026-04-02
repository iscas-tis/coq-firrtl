// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @ClockDomains(in %clock1: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io_errCnt: !firrtl.uint<8>) attributes {convention = #firrtl<convention scalarized>} {
  %io_errCnt_0 = firrtl.wire {name = "io_errCnt"} : !firrtl.uint<8>
  firrtl.strictconnect %io_errCnt, %io_errCnt_0 : !firrtl.uint<8>
  %s_clock, %s_reset, %s_io_c_data, %s_io_c_valid = firrtl.instance s @SourceClock(in clock1: !firrtl.clock, in reset1: !firrtl.uint<1>, out io_c_data: !firrtl.uint<32>, out io_c_valid: !firrtl.uint<1>)
  firrtl.strictconnect %s_clock, %clock1 : !firrtl.clock
  firrtl.strictconnect %s_reset, %reset1 : !firrtl.uint<1>
  %d_clock, %d_reset, %d_io_c_data, %d_io_c_valid, %d_io_errorCnt = firrtl.instance d @SinkClock(in clock1: !firrtl.clock, in reset1: !firrtl.uint<1>, in io_c_data: !firrtl.uint<32>, in io_c_valid: !firrtl.uint<1>, out io_errorCnt: !firrtl.uint<8>)
  %d.io_c_data = firrtl.wire : !firrtl.uint<32>
  %d.io_c_valid = firrtl.wire : !firrtl.uint<1>
  %d.io_errorCnt = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %d_io_c_data, %d.io_c_data : !firrtl.uint<32>
  firrtl.strictconnect %d_io_c_valid, %d.io_c_valid : !firrtl.uint<1>
  firrtl.strictconnect %d.io_errorCnt, %d_io_errorCnt : !firrtl.uint<8>
  firrtl.strictconnect %d_clock, %clock1 : !firrtl.clock
  firrtl.strictconnect %d_reset, %reset1 : !firrtl.uint<1>
  firrtl.strictconnect %d.io_c_data, %s_io_c_data : !firrtl.uint<32>
  firrtl.strictconnect %d.io_c_valid, %s_io_c_valid : !firrtl.uint<1>
  firrtl.strictconnect %io_errCnt_0, %d.io_errorCnt : !firrtl.uint<8>
}

// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module private @SinkClock(in %clock1: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_c_data: !firrtl.uint<32>, in %io_c_valid: !firrtl.uint<1>, out %io_errorCnt: !firrtl.uint<8>) {
  %io_c_data_0 = firrtl.wire {name = "io_c_data"} : !firrtl.uint<32>
  %io_c_valid_1 = firrtl.wire {name = "io_c_valid"} : !firrtl.uint<1>
  %io_errorCnt_2 = firrtl.wire {name = "io_errorCnt"} : !firrtl.uint<8>
  firrtl.strictconnect %io_c_data_0, %io_c_data : !firrtl.uint<32>
  firrtl.strictconnect %io_c_valid_1, %io_c_valid : !firrtl.uint<1>
  firrtl.strictconnect %io_errorCnt, %io_errorCnt_2 : !firrtl.uint<8>
  %c0_ui32 = firrtl.constant 0 : !firrtl.uint<32>
  %expectedCntReg = firrtl.regreset %clock1, %reset1, %c0_ui32 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %c0_ui8 = firrtl.constant 0 : !firrtl.uint<8>
  %errCntReg = firrtl.regreset %clock1, %reset1, %c0_ui8 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>
  %sampleReg = firrtl.regreset %clock1, %reset1, %c0_ui32 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %rising_REG = firrtl.reg %clock1 : !firrtl.clock, !firrtl.uint<1>
  firrtl.strictconnect %rising_REG, %io_c_valid_1 : !firrtl.uint<1>
  %0 = firrtl.eq %rising_REG, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_rising_T = firrtl.node %0 : !firrtl.uint<1>
  %1 = firrtl.and %io_c_valid_1, %_rising_T : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %rising = firrtl.node %1 : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %2 = firrtl.neq %expectedCntReg, %io_c_data_0 : (!firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<1>
  %3 = firrtl.node %2 : !firrtl.uint<1>
  %4 = firrtl.and %rising, %3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %5 = firrtl.add %errCntReg, %c1_ui1 : (!firrtl.uint<8>, !firrtl.uint<1>) -> !firrtl.uint<9>
  %_errCntReg_T = firrtl.node %5 : !firrtl.uint<9>
  %6 = firrtl.tail %_errCntReg_T, 1 : (!firrtl.uint<9>) -> !firrtl.uint<8>
  %_errCntReg_T_1 = firrtl.node %6 : !firrtl.uint<8>
  %7 = firrtl.mux(%3, %_errCntReg_T_1, %errCntReg) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %8 = firrtl.mux(%rising, %7, %errCntReg) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  firrtl.connect %errCntReg, %8 : !firrtl.uint<8>, !firrtl.uint<8>
  %9 = firrtl.mux(%rising, %io_c_data_0, %sampleReg) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %sampleReg, %9 : !firrtl.uint<32>, !firrtl.uint<32>
  %10 = firrtl.add %expectedCntReg, %c1_ui1 : (!firrtl.uint<32>, !firrtl.uint<1>) -> !firrtl.uint<33>
  %_expectedCntReg_T = firrtl.node %10 : !firrtl.uint<33>
  %11 = firrtl.tail %_expectedCntReg_T, 1 : (!firrtl.uint<33>) -> !firrtl.uint<32>
  %_expectedCntReg_T_1 = firrtl.node %11 : !firrtl.uint<32>
  %12 = firrtl.mux(%rising, %_expectedCntReg_T_1, %expectedCntReg) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %expectedCntReg, %12 : !firrtl.uint<32>, !firrtl.uint<32>
  firrtl.strictconnect %io_errorCnt_2, %errCntReg : !firrtl.uint<8>
}

// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module private @SourceClock(in %clock1: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io_c_data: !firrtl.uint<32>, out %io_c_valid: !firrtl.uint<1>) {
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %valid = firrtl.regreset %clock1, %reset1, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>
  %c0_ui32 = firrtl.constant 0 : !firrtl.uint<32>
  %cntReg = firrtl.regreset %clock1, %reset1, %c0_ui32 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %c0_ui2 = firrtl.constant 0 : !firrtl.uint<2>
  %xReg = firrtl.regreset %clock1, %reset1, %c0_ui2 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>
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
  %falling_REG = firrtl.reg %clock1 : !firrtl.clock, !firrtl.uint<1>
  firrtl.strictconnect %falling_REG, %valid : !firrtl.uint<1>
  %4 = firrtl.and %_falling_T, %falling_REG : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %falling = firrtl.node %4 : !firrtl.uint<1>
  %5 = firrtl.add %cntReg, %c1_ui1 : (!firrtl.uint<32>, !firrtl.uint<1>) -> !firrtl.uint<33>
  %_cntReg_T = firrtl.node %5 : !firrtl.uint<33>
  %6 = firrtl.tail %_cntReg_T, 1 : (!firrtl.uint<33>) -> !firrtl.uint<32>
  %_cntReg_T_1 = firrtl.node %6 : !firrtl.uint<32>
  %7 = firrtl.mux(%falling, %_cntReg_T_1, %cntReg) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %cntReg, %7 : !firrtl.uint<32>, !firrtl.uint<32>
  firrtl.strictconnect %io_c_valid, %valid : !firrtl.uint<1>
  firrtl.strictconnect %io_c_data, %cntReg : !firrtl.uint<32>
}

