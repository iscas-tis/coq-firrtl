// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @ParamFunc(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_selA: !firrtl.uint<1>, out %io_resA: !firrtl.uint<5>, in %io_selB: !firrtl.uint<1>, out %io_resB_d: !firrtl.uint<10>, out %io_resB_b: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_selA_0 = firrtl.wire {name = "io_selA"} : !firrtl.uint<1>
  %io_resA_1 = firrtl.wire {name = "io_resA"} : !firrtl.uint<5>
  %io_selB_2 = firrtl.wire {name = "io_selB"} : !firrtl.uint<1>
  %io_resB_d_3 = firrtl.wire {name = "io_resB_d"} : !firrtl.uint<10>
  %io_resB_b_4 = firrtl.wire {name = "io_resB_b"} : !firrtl.uint<1>
  firrtl.strictconnect %io_selA_0, %io_selA : !firrtl.uint<1>
  firrtl.strictconnect %io_resA, %io_resA_1 : !firrtl.uint<5>
  firrtl.strictconnect %io_selB_2, %io_selB : !firrtl.uint<1>
  firrtl.strictconnect %io_resB_d, %io_resB_d_3 : !firrtl.uint<10>
  firrtl.strictconnect %io_resB_b, %io_resB_b_4 : !firrtl.uint<1>
  %resA = firrtl.wire : !firrtl.uint<4>
  %c10_ui4 = firrtl.constant 10 : !firrtl.uint<4>
  %c5_ui3 = firrtl.constant 5 : !firrtl.uint<3>
  %0 = firrtl.mux(%io_selA_0, %c5_ui3, %c10_ui4) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<4>) -> !firrtl.uint<4>
  firrtl.connect %resA, %0 : !firrtl.uint<4>, !firrtl.uint<4>
  %tVal_d = firrtl.wire : !firrtl.uint<10>
  %tVal_b = firrtl.wire : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  firrtl.strictconnect %tVal_b, %c1_ui1 : !firrtl.uint<1>
  %c42_ui6 = firrtl.constant 42 : !firrtl.uint<6>
  %1 = firrtl.pad %c42_ui6, 10 : (!firrtl.uint<6>) -> !firrtl.uint<10>
  firrtl.strictconnect %tVal_d, %1 : !firrtl.uint<10>
  %fVal_d = firrtl.wire : !firrtl.uint<10>
  %fVal_b = firrtl.wire : !firrtl.uint<1>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  firrtl.strictconnect %fVal_b, %c0_ui1 : !firrtl.uint<1>
  %c13_ui4 = firrtl.constant 13 : !firrtl.uint<4>
  %2 = firrtl.pad %c13_ui4, 10 : (!firrtl.uint<4>) -> !firrtl.uint<10>
  firrtl.strictconnect %fVal_d, %2 : !firrtl.uint<10>
  %resB_d = firrtl.wire : !firrtl.uint<10>
  %resB_b = firrtl.wire : !firrtl.uint<1>
  %3 = firrtl.mux(%io_selB_2, %tVal_d, %fVal_d) : (!firrtl.uint<1>, !firrtl.uint<10>, !firrtl.uint<10>) -> !firrtl.uint<10>
  firrtl.connect %resB_d, %3 : !firrtl.uint<10>, !firrtl.uint<10>
  %4 = firrtl.mux(%io_selB_2, %tVal_b, %fVal_b) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.connect %resB_b, %4 : !firrtl.uint<1>, !firrtl.uint<1>
  firrtl.connect %io_resA_1, %resA : !firrtl.uint<5>, !firrtl.uint<4>
  firrtl.strictconnect %io_resB_d_3, %resB_d : !firrtl.uint<10>
  firrtl.strictconnect %io_resB_b_4, %resB_b : !firrtl.uint<1>
}

