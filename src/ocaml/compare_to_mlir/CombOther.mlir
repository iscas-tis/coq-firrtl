// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @CombOther(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_cond: !firrtl.uint<1>, out %io_out: !firrtl.uint<4>) attributes {convention = #firrtl<convention scalarized>} {
  %io_cond_0 = firrtl.wire {name = "io_cond"} : !firrtl.uint<1>
  %io_out_1 = firrtl.wire {name = "io_out"} : !firrtl.uint<4>
  firrtl.strictconnect %io_cond_0, %io_cond : !firrtl.uint<1>
  firrtl.strictconnect %io_out, %io_out_1 : !firrtl.uint<4>
  %w = firrtl.wire : !firrtl.uint<2>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %c2_ui2 = firrtl.constant 2 : !firrtl.uint<2>
  %0 = firrtl.not %io_cond_0 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %1 = firrtl.mux(%io_cond_0, %c1_ui1, %c2_ui2) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<2>
  firrtl.connect %w, %1 : !firrtl.uint<2>, !firrtl.uint<2>
  firrtl.connect %io_out_1, %w : !firrtl.uint<4>, !firrtl.uint<2>
}

