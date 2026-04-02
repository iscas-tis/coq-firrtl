// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @Hello(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io_led: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_led_0 = firrtl.wire {name = "io_led"} : !firrtl.uint<1>
  firrtl.strictconnect %io_led, %io_led_0 : !firrtl.uint<1>
  %c0_ui32 = firrtl.constant 0 : !firrtl.uint<32>
  %cntReg = firrtl.regreset %clock, %reset1, %c0_ui32 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %blkReg = firrtl.regreset %clock, %reset1, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %0 = firrtl.add %cntReg, %c1_ui1 : (!firrtl.uint<32>, !firrtl.uint<1>) -> !firrtl.uint<33>
  %_cntReg_T = firrtl.node %0 : !firrtl.uint<33>
  %1 = firrtl.tail %_cntReg_T, 1 : (!firrtl.uint<33>) -> !firrtl.uint<32>
  %_cntReg_T_1 = firrtl.node %1 : !firrtl.uint<32>
  %c24999999_ui25 = firrtl.constant 24999999 : !firrtl.uint<25>
  %2 = firrtl.eq %cntReg, %c24999999_ui25 : (!firrtl.uint<32>, !firrtl.uint<25>) -> !firrtl.uint<1>
  %3 = firrtl.node %2 : !firrtl.uint<1>
  %4 = firrtl.pad %c0_ui1, 32 : (!firrtl.uint<1>) -> !firrtl.uint<32>
  %5 = firrtl.mux(%3, %4, %_cntReg_T_1) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %cntReg, %5 : !firrtl.uint<32>, !firrtl.uint<32>
  %6 = firrtl.not %blkReg : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %_blkReg_T = firrtl.node %6 : !firrtl.uint<1>
  %7 = firrtl.mux(%3, %_blkReg_T, %blkReg) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.connect %blkReg, %7 : !firrtl.uint<1>, !firrtl.uint<1>
  firrtl.strictconnect %io_led_0, %blkReg : !firrtl.uint<1>
}

