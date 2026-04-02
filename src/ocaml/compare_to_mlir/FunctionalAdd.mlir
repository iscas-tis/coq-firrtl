// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @FunctionalAdd(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_in_0: !firrtl.uint<10>, in %io_in_1: !firrtl.uint<10>, in %io_in_2: !firrtl.uint<10>, in %io_in_3: !firrtl.uint<10>, in %io_in_4: !firrtl.uint<10>, out %io_res: !firrtl.uint<10>) attributes {convention = #firrtl<convention scalarized>} {
  %io_in_0_0 = firrtl.wire {name = "io_in_0"} : !firrtl.uint<10>
  %io_in_1_1 = firrtl.wire {name = "io_in_1"} : !firrtl.uint<10>
  %io_in_2_2 = firrtl.wire {name = "io_in_2"} : !firrtl.uint<10>
  %io_in_3_3 = firrtl.wire {name = "io_in_3"} : !firrtl.uint<10>
  %io_in_4_4 = firrtl.wire {name = "io_in_4"} : !firrtl.uint<10>
  %io_res_5 = firrtl.wire {name = "io_res"} : !firrtl.uint<10>
  firrtl.strictconnect %io_in_0_0, %io_in_0 : !firrtl.uint<10>
  firrtl.strictconnect %io_in_1_1, %io_in_1 : !firrtl.uint<10>
  firrtl.strictconnect %io_in_2_2, %io_in_2 : !firrtl.uint<10>
  firrtl.strictconnect %io_in_3_3, %io_in_3 : !firrtl.uint<10>
  firrtl.strictconnect %io_in_4_4, %io_in_4 : !firrtl.uint<10>
  firrtl.strictconnect %io_res, %io_res_5 : !firrtl.uint<10>
  %0 = firrtl.add %io_in_3_3, %io_in_4_4 : (!firrtl.uint<10>, !firrtl.uint<10>) -> !firrtl.uint<11>
  %_sum_T = firrtl.node %0 : !firrtl.uint<11>
  %1 = firrtl.tail %_sum_T, 1 : (!firrtl.uint<11>) -> !firrtl.uint<10>
  %_sum_T_1 = firrtl.node %1 : !firrtl.uint<10>
  %2 = firrtl.add %io_in_0_0, %io_in_1_1 : (!firrtl.uint<10>, !firrtl.uint<10>) -> !firrtl.uint<11>
  %_sum_T_2 = firrtl.node %2 : !firrtl.uint<11>
  %3 = firrtl.tail %_sum_T_2, 1 : (!firrtl.uint<11>) -> !firrtl.uint<10>
  %_sum_T_3 = firrtl.node %3 : !firrtl.uint<10>
  %4 = firrtl.add %io_in_2_2, %_sum_T_1 : (!firrtl.uint<10>, !firrtl.uint<10>) -> !firrtl.uint<11>
  %_sum_T_4 = firrtl.node %4 : !firrtl.uint<11>
  %5 = firrtl.tail %_sum_T_4, 1 : (!firrtl.uint<11>) -> !firrtl.uint<10>
  %_sum_T_5 = firrtl.node %5 : !firrtl.uint<10>
  %6 = firrtl.add %_sum_T_3, %_sum_T_5 : (!firrtl.uint<10>, !firrtl.uint<10>) -> !firrtl.uint<11>
  %_sum_T_6 = firrtl.node %6 : !firrtl.uint<11>
  %7 = firrtl.tail %_sum_T_6, 1 : (!firrtl.uint<11>) -> !firrtl.uint<10>
  %sum = firrtl.node %7 : !firrtl.uint<10>
  firrtl.strictconnect %io_res_5, %sum : !firrtl.uint<10>
}

