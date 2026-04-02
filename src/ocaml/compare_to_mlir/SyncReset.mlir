// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module private @WhenCounter(in %clock1: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io_cnt: !firrtl.uint<8>, out %io_tick: !firrtl.uint<1>) {
  %c0_ui8 = firrtl.constant 0 : !firrtl.uint<8>
  %cntReg = firrtl.regreset %clock1, %reset1, %c0_ui8 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %0 = firrtl.add %cntReg, %c1_ui1 : (!firrtl.uint<8>, !firrtl.uint<1>) -> !firrtl.uint<9>
  %_cntReg_T = firrtl.node %0 : !firrtl.uint<9>
  %1 = firrtl.tail %_cntReg_T, 1 : (!firrtl.uint<9>) -> !firrtl.uint<8>
  %_cntReg_T_1 = firrtl.node %1 : !firrtl.uint<8>
  %c4_ui3 = firrtl.constant 4 : !firrtl.uint<3>
  %2 = firrtl.eq %cntReg, %c4_ui3 : (!firrtl.uint<8>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %3 = firrtl.node %2 : !firrtl.uint<1>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %4 = firrtl.pad %c0_ui1, 8 : (!firrtl.uint<1>) -> !firrtl.uint<8>
  %5 = firrtl.mux(%3, %4, %_cntReg_T_1) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  firrtl.connect %cntReg, %5 : !firrtl.uint<8>, !firrtl.uint<8>
  %_io_tick_T = firrtl.node %2 : !firrtl.uint<1>
  firrtl.strictconnect %io_tick, %_io_tick_T : !firrtl.uint<1>
  firrtl.strictconnect %io_cnt, %cntReg : !firrtl.uint<8>
}

// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @SyncReset(in %clock1: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io_value: !firrtl.uint<8>) attributes {convention = #firrtl<convention scalarized>} {
  %io_value_0 = firrtl.wire {name = "io_value"} : !firrtl.uint<8>
  firrtl.connect %io_value, %io_value_0 : !firrtl.uint<8>, !firrtl.uint<8>
  %syncReset_REG = firrtl.reg %clock1 : !firrtl.clock, !firrtl.uint<1>
  firrtl.strictconnect %syncReset_REG, %reset1 : !firrtl.uint<1>
  %syncReset = firrtl.reg %clock1 : !firrtl.clock, !firrtl.uint<1>
  firrtl.strictconnect %syncReset, %syncReset_REG : !firrtl.uint<1>
  %cnt_clock, %cnt_reset, %cnt_io_cnt, %cnt_io_tick = firrtl.instance cnt @WhenCounter(in clock1: !firrtl.clock, in reset1: !firrtl.uint<1>, out io_cnt: !firrtl.uint<8>, out io_tick: !firrtl.uint<1>)
  firrtl.strictconnect %cnt_clock, %clock1 : !firrtl.clock
  firrtl.strictconnect %cnt_reset, %syncReset : !firrtl.uint<1>
  firrtl.connect %io_value_0, %cnt_io_cnt : !firrtl.uint<8>, !firrtl.uint<8>
}

