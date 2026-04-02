// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @ReadyValidBuffer(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io_in_ready: !firrtl.uint<1>, in %io_in_valid: !firrtl.uint<1>, in %io_in_bits1: !firrtl.uint<8>, in %io_out_ready: !firrtl.uint<1>, out %io_out_valid: !firrtl.uint<1>, out %io_out_bits1: !firrtl.uint<8>) attributes {convention = #firrtl<convention scalarized>} {
  %io_in_ready_0 = firrtl.wire {name = "io_in_ready"} : !firrtl.uint<1>
  %io_in_valid_1 = firrtl.wire {name = "io_in_valid"} : !firrtl.uint<1>
  %io_in_bits1_2 = firrtl.wire {name = "io_in_bits1"} : !firrtl.uint<8>
  %io_out_ready_3 = firrtl.wire {name = "io_out_ready"} : !firrtl.uint<1>
  %io_out_valid_4 = firrtl.wire {name = "io_out_valid"} : !firrtl.uint<1>
  %io_out_bits1_5 = firrtl.wire {name = "io_out_bits1"} : !firrtl.uint<8>
  firrtl.strictconnect %io_in_ready, %io_in_ready_0 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_valid_1, %io_in_valid : !firrtl.uint<1>
  firrtl.strictconnect %io_in_bits1_2, %io_in_bits1 : !firrtl.uint<8>
  firrtl.strictconnect %io_out_ready_3, %io_out_ready : !firrtl.uint<1>
  firrtl.strictconnect %io_out_valid, %io_out_valid_4 : !firrtl.uint<1>
  firrtl.strictconnect %io_out_bits1, %io_out_bits1_5 : !firrtl.uint<8>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %dataReg = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<8>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %emptyReg = firrtl.regreset %clock, %reset1, %c1_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>
  firrtl.strictconnect %io_in_ready_0, %emptyReg : !firrtl.uint<1>
  %0 = firrtl.eq %emptyReg, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_valid_T = firrtl.node %0 : !firrtl.uint<1>
  firrtl.strictconnect %io_out_valid_4, %_io_out_valid_T : !firrtl.uint<1>
  firrtl.strictconnect %io_out_bits1_5, %dataReg : !firrtl.uint<8>
  %1 = firrtl.and %emptyReg, %io_in_valid_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %2 = firrtl.node %1 : !firrtl.uint<1>
  %3 = firrtl.mux(%2, %io_in_bits1_2, %dataReg) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  firrtl.connect %dataReg, %3 : !firrtl.uint<8>, !firrtl.uint<8>
  %4 = firrtl.mux(%2, %c0_ui1, %emptyReg) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %5 = firrtl.node %0 : !firrtl.uint<1>
  %6 = firrtl.and %5, %io_out_ready_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %7 = firrtl.node %6 : !firrtl.uint<1>
  %8 = firrtl.mux(%7, %c1_ui1, %4) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.connect %emptyReg, %8 : !firrtl.uint<1>, !firrtl.uint<1>
}

