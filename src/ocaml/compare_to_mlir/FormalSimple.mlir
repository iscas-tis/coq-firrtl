// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @FormalSimple(in %clock1: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_a: !firrtl.uint<10>, in %io_b: !firrtl.uint<10>, out %io_y: !firrtl.uint<10>) attributes {convention = #firrtl<convention scalarized>} {
  %io_a_0 = firrtl.wire {name = "io_a"} : !firrtl.uint<10>
  %io_b_1 = firrtl.wire {name = "io_b"} : !firrtl.uint<10>
  %io_y_2 = firrtl.wire {name = "io_y"} : !firrtl.uint<10>
  firrtl.strictconnect %io_a_0, %io_a : !firrtl.uint<10>
  firrtl.strictconnect %io_b_1, %io_b : !firrtl.uint<10>
  firrtl.strictconnect %io_y, %io_y_2 : !firrtl.uint<10>
  %0 = firrtl.and %io_a_0, %io_b_1 : (!firrtl.uint<10>, !firrtl.uint<10>) -> !firrtl.uint<10>
  %_io_y_T = firrtl.node %0 : !firrtl.uint<10>
  firrtl.strictconnect %io_y_2, %_io_y_T : !firrtl.uint<10>
}
