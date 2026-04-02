// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @CombWhen2Untested(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_data: !firrtl.uint<4>, out %io_out: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_data_0 = firrtl.wire {name = "io_data"} : !firrtl.uint<4>
  %io_out_1 = firrtl.wire {name = "io_out"} : !firrtl.uint<1>
  firrtl.strictconnect %io_data_0, %io_data : !firrtl.uint<4>
  firrtl.strictconnect %io_out, %io_out_1 : !firrtl.uint<1>
  %enoughMoney = firrtl.wire : !firrtl.uint<1>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %c5_ui3 = firrtl.constant 5 : !firrtl.uint<3>
  %0 = firrtl.geq %io_data_0, %c5_ui3 : (!firrtl.uint<4>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %1 = firrtl.node %0 : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  firrtl.connect %enoughMoney, %1 : !firrtl.uint<1>, !firrtl.uint<1>
  firrtl.strictconnect %io_out_1, %enoughMoney : !firrtl.uint<1>
}

