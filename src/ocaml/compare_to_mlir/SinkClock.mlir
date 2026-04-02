// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @SinkClock(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_c_data: !firrtl.uint<32>, in %io_c_valid: !firrtl.uint<1>, out %io_errorCnt: !firrtl.uint<8>) attributes {convention = #firrtl<convention scalarized>} {
  %io_c_data_0 = firrtl.wire {name = "io_c_data"} : !firrtl.uint<32>
  %io_c_valid_1 = firrtl.wire {name = "io_c_valid"} : !firrtl.uint<1>
  %io_errorCnt_2 = firrtl.wire {name = "io_errorCnt"} : !firrtl.uint<8>
  firrtl.strictconnect %io_c_data_0, %io_c_data : !firrtl.uint<32>
  firrtl.strictconnect %io_c_valid_1, %io_c_valid : !firrtl.uint<1>
  firrtl.strictconnect %io_errorCnt, %io_errorCnt_2 : !firrtl.uint<8>
  %c0_ui32 = firrtl.constant 0 : !firrtl.uint<32>
  %expectedCntReg = firrtl.regreset %clock, %reset1, %c0_ui32 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %c0_ui8 = firrtl.constant 0 : !firrtl.uint<8>
  %errCntReg = firrtl.regreset %clock, %reset1, %c0_ui8 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>
  %sampleReg = firrtl.regreset %clock, %reset1, %c0_ui32 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %rising_REG = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
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

