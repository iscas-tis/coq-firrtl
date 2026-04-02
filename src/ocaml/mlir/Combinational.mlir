// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @Combinational(in %clock1: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_a: !firrtl.uint<4>, in %io_b: !firrtl.uint<4>, in %io_c: !firrtl.uint<4>, out %io_out: !firrtl.uint<4>, out %io_out2: !firrtl.uint<4>) attributes {convention = #firrtl<convention scalarized>} {
  %io_a_0 = firrtl.wire {name = "io_a"} : !firrtl.uint<4>
  %io_b_1 = firrtl.wire {name = "io_b"} : !firrtl.uint<4>
  %io_c_2 = firrtl.wire {name = "io_c"} : !firrtl.uint<4>
  %io_out_3 = firrtl.wire {name = "io_out"} : !firrtl.uint<4>
  %io_out2_4 = firrtl.wire {name = "io_out2"} : !firrtl.uint<4>
  firrtl.strictconnect %io_a_0, %io_a : !firrtl.uint<4>
  firrtl.strictconnect %io_b_1, %io_b : !firrtl.uint<4>
  firrtl.strictconnect %io_c_2, %io_c : !firrtl.uint<4>
  firrtl.strictconnect %io_out, %io_out_3 : !firrtl.uint<4>
  firrtl.strictconnect %io_out2, %io_out2_4 : !firrtl.uint<4>
  %0 = firrtl.and %io_a_0, %io_b_1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_e_T = firrtl.node %0 : !firrtl.uint<4>
  %1 = firrtl.or %_e_T, %io_c_2 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %e = firrtl.node %1 : !firrtl.uint<4>
  %2 = firrtl.not %e : (!firrtl.uint<4>) -> !firrtl.uint<4>
  %f = firrtl.node %2 : !firrtl.uint<4>
  firrtl.strictconnect %io_out_3, %e : !firrtl.uint<4>
  firrtl.strictconnect %io_out2_4, %f : !firrtl.uint<4>
}

