// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @ShiftRegister(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_din: !firrtl.uint<1>, out %io_dout: !firrtl.uint<1>, in %io_serIn: !firrtl.uint<1>, out %io_paraOut: !firrtl.uint<4>, in %io_d: !firrtl.uint<4>, in %io_load: !firrtl.uint<1>, out %io_serOut: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_din_0 = firrtl.wire {name = "io_din"} : !firrtl.uint<1>
  %io_dout_1 = firrtl.wire {name = "io_dout"} : !firrtl.uint<1>
  %io_serIn_2 = firrtl.wire {name = "io_serIn"} : !firrtl.uint<1>
  %io_paraOut_3 = firrtl.wire {name = "io_paraOut"} : !firrtl.uint<4>
  %io_d_4 = firrtl.wire {name = "io_d"} : !firrtl.uint<4>
  %io_load_5 = firrtl.wire {name = "io_load"} : !firrtl.uint<1>
  %io_serOut_6 = firrtl.wire {name = "io_serOut"} : !firrtl.uint<1>
  firrtl.strictconnect %io_din_0, %io_din : !firrtl.uint<1>
  firrtl.strictconnect %io_dout, %io_dout_1 : !firrtl.uint<1>
  firrtl.strictconnect %io_serIn_2, %io_serIn : !firrtl.uint<1>
  firrtl.strictconnect %io_paraOut, %io_paraOut_3 : !firrtl.uint<4>
  firrtl.strictconnect %io_d_4, %io_d : !firrtl.uint<4>
  firrtl.strictconnect %io_load_5, %io_load : !firrtl.uint<1>
  firrtl.strictconnect %io_serOut, %io_serOut_6 : !firrtl.uint<1>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %shiftReg = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<4>
  %0 = firrtl.bits %shiftReg 2 to 0 : (!firrtl.uint<4>) -> !firrtl.uint<3>
  %_shiftReg_T = firrtl.node %0 : !firrtl.uint<3>
  %1 = firrtl.cat %_shiftReg_T, %io_din_0 : (!firrtl.uint<3>, !firrtl.uint<1>) -> !firrtl.uint<4>
  %_shiftReg_T_1 = firrtl.node %1 : !firrtl.uint<4>
  firrtl.strictconnect %shiftReg, %_shiftReg_T_1 : !firrtl.uint<4>
  %2 = firrtl.bits %shiftReg 3 to 3 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %dout = firrtl.node %2 : !firrtl.uint<1>
  %c0_ui4 = firrtl.constant 0 : !firrtl.uint<4>
  %outReg = firrtl.regreset %clock, %reset1, %c0_ui4 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>
  %3 = firrtl.bits %outReg 3 to 1 : (!firrtl.uint<4>) -> !firrtl.uint<3>
  %_outReg_T = firrtl.node %3 : !firrtl.uint<3>
  %4 = firrtl.cat %io_serIn_2, %_outReg_T : (!firrtl.uint<1>, !firrtl.uint<3>) -> !firrtl.uint<4>
  %_outReg_T_1 = firrtl.node %4 : !firrtl.uint<4>
  firrtl.strictconnect %outReg, %_outReg_T_1 : !firrtl.uint<4>
  %loadReg = firrtl.regreset %clock, %reset1, %c0_ui4 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>
  %5 = firrtl.not %io_load_5 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %6 = firrtl.bits %loadReg 3 to 1 : (!firrtl.uint<4>) -> !firrtl.uint<3>
  %_loadReg_T = firrtl.node %6 : !firrtl.uint<3>
  %7 = firrtl.cat %c0_ui1, %_loadReg_T : (!firrtl.uint<1>, !firrtl.uint<3>) -> !firrtl.uint<4>
  %_loadReg_T_1 = firrtl.node %7 : !firrtl.uint<4>
  %8 = firrtl.mux(%io_load_5, %io_d_4, %_loadReg_T_1) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  firrtl.connect %loadReg, %8 : !firrtl.uint<4>, !firrtl.uint<4>
  %9 = firrtl.bits %loadReg 0 to 0 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %serOut = firrtl.node %9 : !firrtl.uint<1>
  firrtl.strictconnect %io_serOut_6, %serOut : !firrtl.uint<1>
  firrtl.strictconnect %io_paraOut_3, %outReg : !firrtl.uint<4>
  firrtl.strictconnect %io_dout_1, %dout : !firrtl.uint<1>
}

