// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @Registers(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_in: !firrtl.uint<8>, out %io_out: !firrtl.uint<8>) attributes {convention = #firrtl<convention scalarized>} {
  %io_in_0 = firrtl.wire {name = "io_in"} : !firrtl.uint<8>
  %io_out_1 = firrtl.wire {name = "io_out"} : !firrtl.uint<8>
  firrtl.strictconnect %io_in_0, %io_in : !firrtl.uint<8>
  firrtl.strictconnect %io_out, %io_out_1 : !firrtl.uint<8>
  %c0_ui8 = firrtl.constant 0 : !firrtl.uint<8>
  %q = firrtl.regreset %clock, %reset1, %c0_ui8 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>
  firrtl.strictconnect %q, %io_in_0 : !firrtl.uint<8>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %nextReg = firrtl.regreset %clock, %c0_ui1, %q : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>
  firrtl.connect %nextReg, %io_in_0 : !firrtl.uint<8>, !firrtl.uint<8>
  %bothReg = firrtl.regreset %clock, %reset1, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<8>
  firrtl.connect %bothReg, %io_in_0 : !firrtl.uint<8>, !firrtl.uint<8>
  firrtl.strictconnect %io_out_1, %q : !firrtl.uint<8>
}

