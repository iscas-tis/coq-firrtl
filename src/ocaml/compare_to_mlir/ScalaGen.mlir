// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @ScalaGen(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_din: !firrtl.uint<1>, out %io_dout: !firrtl.uint<8>) attributes {convention = #firrtl<convention scalarized>} {
  %io_din_0 = firrtl.wire {name = "io_din"} : !firrtl.uint<1>
  %io_dout_1 = firrtl.wire {name = "io_dout"} : !firrtl.uint<8>
  firrtl.strictconnect %io_din_0, %io_din : !firrtl.uint<1>
  firrtl.strictconnect %io_dout, %io_dout_1 : !firrtl.uint<8>
  %regVec_0 = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
  %regVec_1 = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
  %regVec_2 = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
  %regVec_3 = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
  %regVec_4 = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
  %regVec_5 = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
  %regVec_6 = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
  %regVec_7 = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
  firrtl.strictconnect %regVec_0, %io_din_0 : !firrtl.uint<1>
  firrtl.strictconnect %regVec_1, %regVec_0 : !firrtl.uint<1>
  firrtl.strictconnect %regVec_2, %regVec_1 : !firrtl.uint<1>
  firrtl.strictconnect %regVec_3, %regVec_2 : !firrtl.uint<1>
  firrtl.strictconnect %regVec_4, %regVec_3 : !firrtl.uint<1>
  firrtl.strictconnect %regVec_5, %regVec_4 : !firrtl.uint<1>
  firrtl.strictconnect %regVec_6, %regVec_5 : !firrtl.uint<1>
  firrtl.strictconnect %regVec_7, %regVec_6 : !firrtl.uint<1>
  %0 = firrtl.cat %regVec_1, %regVec_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %io_dout_lo_lo = firrtl.node %0 : !firrtl.uint<2>
  %1 = firrtl.cat %regVec_3, %regVec_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %io_dout_lo_hi = firrtl.node %1 : !firrtl.uint<2>
  %2 = firrtl.cat %io_dout_lo_hi, %io_dout_lo_lo : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<4>
  %io_dout_lo = firrtl.node %2 : !firrtl.uint<4>
  %3 = firrtl.cat %regVec_5, %regVec_4 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %io_dout_hi_lo = firrtl.node %3 : !firrtl.uint<2>
  %4 = firrtl.cat %regVec_7, %regVec_6 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %io_dout_hi_hi = firrtl.node %4 : !firrtl.uint<2>
  %5 = firrtl.cat %io_dout_hi_hi, %io_dout_hi_lo : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<4>
  %io_dout_hi = firrtl.node %5 : !firrtl.uint<4>
  %6 = firrtl.cat %io_dout_hi, %io_dout_lo : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>
  %_io_dout_T = firrtl.node %6 : !firrtl.uint<8>
  firrtl.strictconnect %io_dout_1, %_io_dout_T : !firrtl.uint<8>
}

