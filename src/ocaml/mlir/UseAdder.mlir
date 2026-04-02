// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module private @ParamAdder(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %io_a: !firrtl.uint<8>, in %io_b: !firrtl.uint<8>, out %io_c: !firrtl.uint<8>) {
  %io_a_0 = firrtl.wire {name = "io_a"} : !firrtl.uint<8>
  %io_b_1 = firrtl.wire {name = "io_b"} : !firrtl.uint<8>
  %io_c_2 = firrtl.wire {name = "io_c"} : !firrtl.uint<8>
  firrtl.strictconnect %io_a_0, %io_a : !firrtl.uint<8>
  firrtl.strictconnect %io_b_1, %io_b : !firrtl.uint<8>
  firrtl.strictconnect %io_c, %io_c_2 : !firrtl.uint<8>
  %0 = firrtl.add %io_a_0, %io_b_1 : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<9>
  %_io_c_T = firrtl.node %0 : !firrtl.uint<9>
  %1 = firrtl.tail %_io_c_T, 1 : (!firrtl.uint<9>) -> !firrtl.uint<8>
  %_io_c_T_1 = firrtl.node %1 : !firrtl.uint<8>
  firrtl.strictconnect %io_c_2, %_io_c_T_1 : !firrtl.uint<8>
}

// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module private @ParamAdder_1(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %io_a: !firrtl.uint<16>, in %io_b: !firrtl.uint<16>, out %io_c: !firrtl.uint<16>) {
  %io_a_0 = firrtl.wire {name = "io_a"} : !firrtl.uint<16>
  %io_b_1 = firrtl.wire {name = "io_b"} : !firrtl.uint<16>
  %io_c_2 = firrtl.wire {name = "io_c"} : !firrtl.uint<16>
  firrtl.strictconnect %io_a_0, %io_a : !firrtl.uint<16>
  firrtl.strictconnect %io_b_1, %io_b : !firrtl.uint<16>
  firrtl.strictconnect %io_c, %io_c_2 : !firrtl.uint<16>
  %0 = firrtl.add %io_a_0, %io_b_1 : (!firrtl.uint<16>, !firrtl.uint<16>) -> !firrtl.uint<17>
  %_io_c_T = firrtl.node %0 : !firrtl.uint<17>
  %1 = firrtl.tail %_io_c_T, 1 : (!firrtl.uint<17>) -> !firrtl.uint<16>
  %_io_c_T_1 = firrtl.node %1 : !firrtl.uint<16>
  firrtl.strictconnect %io_c_2, %_io_c_T_1 : !firrtl.uint<16>
}

// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @UseAdder(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %io_x: !firrtl.uint<16>, in %io_y: !firrtl.uint<16>, out %io_res: !firrtl.uint<16>) attributes {convention = #firrtl<convention scalarized>} {
  %io_x_0 = firrtl.wire {name = "io_x"} : !firrtl.uint<16>
  %io_y_1 = firrtl.wire {name = "io_y"} : !firrtl.uint<16>
  %io_res_2 = firrtl.wire {name = "io_res"} : !firrtl.uint<16>
  firrtl.strictconnect %io_x_0, %io_x : !firrtl.uint<16>
  firrtl.strictconnect %io_y_1, %io_y : !firrtl.uint<16>
  firrtl.strictconnect %io_res, %io_res_2 : !firrtl.uint<16>
  %add8_clock, %add8_reset, %add8_io_a, %add8_io_b, %add8_io_c = firrtl.instance add8 @ParamAdder(in clock: !firrtl.clock, in reset: !firrtl.uint<1>, in io_a: !firrtl.uint<8>, in io_b: !firrtl.uint<8>, out io_c: !firrtl.uint<8>)
  %add8.io_a = firrtl.wire : !firrtl.uint<8>
  %add8.io_b = firrtl.wire : !firrtl.uint<8>
  %add8.io_c = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %add8_io_a, %add8.io_a : !firrtl.uint<8>
  firrtl.strictconnect %add8_io_b, %add8.io_b : !firrtl.uint<8>
  firrtl.strictconnect %add8.io_c, %add8_io_c : !firrtl.uint<8>
  firrtl.strictconnect %add8_clock, %clock : !firrtl.clock
  firrtl.strictconnect %add8_reset, %reset : !firrtl.uint<1>
  %add16_clock, %add16_reset, %add16_io_a, %add16_io_b, %add16_io_c = firrtl.instance add16 @ParamAdder_1(in clock: !firrtl.clock, in reset: !firrtl.uint<1>, in io_a: !firrtl.uint<16>, in io_b: !firrtl.uint<16>, out io_c: !firrtl.uint<16>)
  %add16.io_a = firrtl.wire : !firrtl.uint<16>
  %add16.io_b = firrtl.wire : !firrtl.uint<16>
  %add16.io_c = firrtl.wire : !firrtl.uint<16>
  firrtl.strictconnect %add16_io_a, %add16.io_a : !firrtl.uint<16>
  firrtl.strictconnect %add16_io_b, %add16.io_b : !firrtl.uint<16>
  firrtl.strictconnect %add16.io_c, %add16_io_c : !firrtl.uint<16>
  firrtl.strictconnect %add16_clock, %clock : !firrtl.clock
  firrtl.strictconnect %add16_reset, %reset : !firrtl.uint<1>
  firrtl.strictconnect %add16.io_a, %io_x_0 : !firrtl.uint<16>
  firrtl.strictconnect %add16.io_b, %io_y_1 : !firrtl.uint<16>
  %0 = firrtl.or %add16.io_c, %add8.io_c : (!firrtl.uint<16>, !firrtl.uint<8>) -> !firrtl.uint<16>
  %_io_res_T = firrtl.node %0 : !firrtl.uint<16>
  firrtl.strictconnect %io_res_2, %_io_res_T : !firrtl.uint<16>
  %1 = firrtl.tail %io_x_0, 8 : (!firrtl.uint<16>) -> !firrtl.uint<8>
  firrtl.strictconnect %add8.io_a, %1 : !firrtl.uint<8>
  %2 = firrtl.tail %io_y_1, 8 : (!firrtl.uint<16>) -> !firrtl.uint<8>
  firrtl.strictconnect %add8.io_b, %2 : !firrtl.uint<8>
}

