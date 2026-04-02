// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @UIntVsU(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io_values_0: !firrtl.uint<3>, out %io_values_1: !firrtl.uint<3>, out %io_values_2: !firrtl.uint<3>, out %io_values_3: !firrtl.uint<3>, out %io_values_4: !firrtl.uint<3>) attributes {convention = #firrtl<convention scalarized>} {
  %io_values_0_0 = firrtl.wire {name = "io_values_0"} : !firrtl.uint<3>
  %io_values_1_1 = firrtl.wire {name = "io_values_1"} : !firrtl.uint<3>
  %io_values_2_2 = firrtl.wire {name = "io_values_2"} : !firrtl.uint<3>
  %io_values_3_3 = firrtl.wire {name = "io_values_3"} : !firrtl.uint<3>
  %io_values_4_4 = firrtl.wire {name = "io_values_4"} : !firrtl.uint<3>
  firrtl.strictconnect %io_values_0, %io_values_0_0 : !firrtl.uint<3>
  firrtl.strictconnect %io_values_1, %io_values_1_1 : !firrtl.uint<3>
  firrtl.strictconnect %io_values_2, %io_values_2_2 : !firrtl.uint<3>
  firrtl.strictconnect %io_values_3, %io_values_3_3 : !firrtl.uint<3>
  firrtl.strictconnect %io_values_4, %io_values_4_4 : !firrtl.uint<3>
  %c7_ui3 = firrtl.constant 7 : !firrtl.uint<3>
  firrtl.strictconnect %io_values_0_0, %c7_ui3 : !firrtl.uint<3>
  firrtl.strictconnect %io_values_1_1, %c7_ui3 : !firrtl.uint<3>
  firrtl.strictconnect %io_values_2_2, %c7_ui3 : !firrtl.uint<3>
  firrtl.strictconnect %io_values_3_3, %c7_ui3 : !firrtl.uint<3>
  %signed = firrtl.wire : !firrtl.sint<3>
  %0 = firrtl.asSInt %c7_ui3 : (!firrtl.uint<3>) -> !firrtl.sint<3>
  firrtl.strictconnect %signed, %0 : !firrtl.sint<3>
  %1 = firrtl.asUInt %signed : (!firrtl.sint<3>) -> !firrtl.uint<3>
  %_io_values_4_T = firrtl.node %1 : !firrtl.uint<3>
  firrtl.strictconnect %io_values_4_4, %_io_values_4_T : !firrtl.uint<3>
}

