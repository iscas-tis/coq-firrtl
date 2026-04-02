// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @BasicExercise(in %clock1: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_sw: !firrtl.uint<2>, out %io_led: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_sw_0 = firrtl.wire {name = "io_sw"} : !firrtl.uint<2>
  %io_led_1 = firrtl.wire {name = "io_led"} : !firrtl.uint<1>
  firrtl.strictconnect %io_sw_0, %io_sw : !firrtl.uint<2>
  firrtl.strictconnect %io_led, %io_led_1 : !firrtl.uint<1>
  %0 = firrtl.bits %io_sw_0 0 to 0 : (!firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_led_T = firrtl.node %0 : !firrtl.uint<1>
  %1 = firrtl.bits %io_sw_0 1 to 1 : (!firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_led_T_1 = firrtl.node %1 : !firrtl.uint<1>
  %2 = firrtl.and %_io_led_T, %_io_led_T_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_led_T_2 = firrtl.node %2 : !firrtl.uint<1>
  firrtl.strictconnect %io_led_1, %_io_led_T_2 : !firrtl.uint<1>
}

