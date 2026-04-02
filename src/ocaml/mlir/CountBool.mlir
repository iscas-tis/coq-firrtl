// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @CountBool(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_in_0: !firrtl.uint<1>, in %io_in_1: !firrtl.uint<1>, in %io_in_2: !firrtl.uint<1>, in %io_in_3: !firrtl.uint<1>, in %io_in_4: !firrtl.uint<1>, in %io_in_5: !firrtl.uint<1>, in %io_in_6: !firrtl.uint<1>, in %io_in_7: !firrtl.uint<1>, in %io_in_8: !firrtl.uint<1>, out %io_out: !firrtl.uint<4>) attributes {convention = #firrtl<convention scalarized>} {
  %io_in_0_0 = firrtl.wire {name = "io_in_0"} : !firrtl.uint<1>
  %io_in_1_1 = firrtl.wire {name = "io_in_1"} : !firrtl.uint<1>
  %io_in_2_2 = firrtl.wire {name = "io_in_2"} : !firrtl.uint<1>
  %io_in_3_3 = firrtl.wire {name = "io_in_3"} : !firrtl.uint<1>
  %io_in_4_4 = firrtl.wire {name = "io_in_4"} : !firrtl.uint<1>
  %io_in_5_5 = firrtl.wire {name = "io_in_5"} : !firrtl.uint<1>
  %io_in_6_6 = firrtl.wire {name = "io_in_6"} : !firrtl.uint<1>
  %io_in_7_7 = firrtl.wire {name = "io_in_7"} : !firrtl.uint<1>
  %io_in_8_8 = firrtl.wire {name = "io_in_8"} : !firrtl.uint<1>
  %io_out_9 = firrtl.wire {name = "io_out"} : !firrtl.uint<4>
  firrtl.strictconnect %io_in_0_0, %io_in_0 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_1_1, %io_in_1 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_2_2, %io_in_2 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_3_3, %io_in_3 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_4_4, %io_in_4 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_5_5, %io_in_5 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_6_6, %io_in_6 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_7_7, %io_in_7 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_8_8, %io_in_8 : !firrtl.uint<1>
  firrtl.strictconnect %io_out, %io_out_9 : !firrtl.uint<4>
  %0 = firrtl.add %io_in_0_0, %io_in_1_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %_io_out_T = firrtl.node %0 : !firrtl.uint<2>
  %1 = firrtl.bits %_io_out_T 1 to 0 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_1 = firrtl.node %1 : !firrtl.uint<2>
  %2 = firrtl.add %io_in_2_2, %io_in_3_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %_io_out_T_2 = firrtl.node %2 : !firrtl.uint<2>
  %3 = firrtl.bits %_io_out_T_2 1 to 0 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_3 = firrtl.node %3 : !firrtl.uint<2>
  %4 = firrtl.add %_io_out_T_1, %_io_out_T_3 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<3>
  %_io_out_T_4 = firrtl.node %4 : !firrtl.uint<3>
  %5 = firrtl.bits %_io_out_T_4 2 to 0 : (!firrtl.uint<3>) -> !firrtl.uint<3>
  %_io_out_T_5 = firrtl.node %5 : !firrtl.uint<3>
  %6 = firrtl.add %io_in_4_4, %io_in_5_5 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %_io_out_T_6 = firrtl.node %6 : !firrtl.uint<2>
  %7 = firrtl.bits %_io_out_T_6 1 to 0 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_7 = firrtl.node %7 : !firrtl.uint<2>
  %8 = firrtl.add %io_in_7_7, %io_in_8_8 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %_io_out_T_8 = firrtl.node %8 : !firrtl.uint<2>
  %9 = firrtl.bits %_io_out_T_8 1 to 0 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_9 = firrtl.node %9 : !firrtl.uint<2>
  %10 = firrtl.add %io_in_6_6, %_io_out_T_9 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<3>
  %_io_out_T_10 = firrtl.node %10 : !firrtl.uint<3>
  %11 = firrtl.bits %_io_out_T_10 1 to 0 : (!firrtl.uint<3>) -> !firrtl.uint<2>
  %_io_out_T_11 = firrtl.node %11 : !firrtl.uint<2>
  %12 = firrtl.add %_io_out_T_7, %_io_out_T_11 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<3>
  %_io_out_T_12 = firrtl.node %12 : !firrtl.uint<3>
  %13 = firrtl.bits %_io_out_T_12 2 to 0 : (!firrtl.uint<3>) -> !firrtl.uint<3>
  %_io_out_T_13 = firrtl.node %13 : !firrtl.uint<3>
  %14 = firrtl.add %_io_out_T_5, %_io_out_T_13 : (!firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<4>
  %_io_out_T_14 = firrtl.node %14 : !firrtl.uint<4>
  %15 = firrtl.bits %_io_out_T_14 3 to 0 : (!firrtl.uint<4>) -> !firrtl.uint<4>
  %_io_out_T_15 = firrtl.node %15 : !firrtl.uint<4>
  firrtl.strictconnect %io_out_9, %_io_out_T_15 : !firrtl.uint<4>
}

