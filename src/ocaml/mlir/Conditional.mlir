// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @Conditional(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_condition: !firrtl.uint<1>, out %io_result: !firrtl.uint<4>) attributes {convention = #firrtl<convention scalarized>} {
  %io_condition_0 = firrtl.wire {name = "io_condition"} : !firrtl.uint<1>
  %io_result_1 = firrtl.wire {name = "io_result"} : !firrtl.uint<4>
  firrtl.strictconnect %io_condition_0, %io_condition : !firrtl.uint<1>
  firrtl.strictconnect %io_result, %io_result_1 : !firrtl.uint<4>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %0 = firrtl.eq %io_condition_0, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %c1 = firrtl.node %0 : !firrtl.uint<1>
  %c2 = firrtl.node %0 : !firrtl.uint<1>
  %v = firrtl.wire : !firrtl.uint<3>
  %c5_ui3 = firrtl.constant 5 : !firrtl.uint<3>
  %1 = firrtl.mux(%io_condition_0, %c0_ui1, %c5_ui3) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %2 = firrtl.mux(%c1, %c1_ui1, %1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %c2_ui2 = firrtl.constant 2 : !firrtl.uint<2>
  %3 = firrtl.mux(%c2, %c2_ui2, %2) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
  %4 = firrtl.not %c1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %5 = firrtl.and %4, %c2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %6 = firrtl.not %c2 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %7 = firrtl.and %4, %6 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %8 = firrtl.mux(%c2, %c2_ui2, %c3_ui2) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %9 = firrtl.mux(%c1, %c1_ui1, %8) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<2>
  firrtl.connect %v, %9 : !firrtl.uint<3>, !firrtl.uint<2>
  firrtl.connect %io_result_1, %v : !firrtl.uint<4>, !firrtl.uint<3>
}

