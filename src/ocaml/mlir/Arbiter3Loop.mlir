// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @Arbiter3Loop(in %clock1: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_request: !firrtl.uint<3>, out %io_grant: !firrtl.uint<3>) attributes {convention = #firrtl<convention scalarized>} {
  %io_request_0 = firrtl.wire {name = "io_request"} : !firrtl.uint<3>
  %io_grant_1 = firrtl.wire {name = "io_grant"} : !firrtl.uint<3>
  firrtl.strictconnect %io_request_0, %io_request : !firrtl.uint<3>
  firrtl.strictconnect %io_grant, %io_grant_1 : !firrtl.uint<3>
  %0 = firrtl.bits %io_request_0 0 to 0 : (!firrtl.uint<3>) -> !firrtl.uint<1>
  %_request_T = firrtl.node %0 : !firrtl.uint<1>
  %1 = firrtl.bits %io_request_0 1 to 1 : (!firrtl.uint<3>) -> !firrtl.uint<1>
  %_request_T_1 = firrtl.node %1 : !firrtl.uint<1>
  %2 = firrtl.bits %io_request_0 2 to 2 : (!firrtl.uint<3>) -> !firrtl.uint<1>
  %_request_T_2 = firrtl.node %2 : !firrtl.uint<1>
  %request_0 = firrtl.wire : !firrtl.uint<1>
  %request_1 = firrtl.wire : !firrtl.uint<1>
  %request_2 = firrtl.wire : !firrtl.uint<1>
  firrtl.strictconnect %request_0, %_request_T : !firrtl.uint<1>
  firrtl.strictconnect %request_1, %_request_T_1 : !firrtl.uint<1>
  firrtl.strictconnect %request_2, %_request_T_2 : !firrtl.uint<1>
  %grant_0 = firrtl.wire : !firrtl.uint<1>
  %grant_1 = firrtl.wire : !firrtl.uint<1>
  %grant_2 = firrtl.wire : !firrtl.uint<1>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %notGranted_0 = firrtl.wire : !firrtl.uint<1>
  %notGranted_1 = firrtl.wire : !firrtl.uint<1>
  %notGranted_2 = firrtl.wire : !firrtl.uint<1>
  firrtl.strictconnect %grant_0, %request_0 : !firrtl.uint<1>
  %3 = firrtl.eq %grant_0, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_notGranted_0_T = firrtl.node %3 : !firrtl.uint<1>
  firrtl.strictconnect %notGranted_0, %_notGranted_0_T : !firrtl.uint<1>
  %4 = firrtl.and %request_1, %notGranted_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_grant_1_T = firrtl.node %4 : !firrtl.uint<1>
  firrtl.strictconnect %grant_1, %_grant_1_T : !firrtl.uint<1>
  %5 = firrtl.eq %grant_1, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_notGranted_1_T = firrtl.node %5 : !firrtl.uint<1>
  %6 = firrtl.and %_notGranted_1_T, %notGranted_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_notGranted_1_T_1 = firrtl.node %6 : !firrtl.uint<1>
  firrtl.strictconnect %notGranted_1, %_notGranted_1_T_1 : !firrtl.uint<1>
  %7 = firrtl.and %request_2, %notGranted_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_grant_2_T = firrtl.node %7 : !firrtl.uint<1>
  firrtl.strictconnect %grant_2, %_grant_2_T : !firrtl.uint<1>
  %8 = firrtl.eq %grant_2, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_notGranted_2_T = firrtl.node %8 : !firrtl.uint<1>
  %9 = firrtl.and %_notGranted_2_T, %notGranted_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_notGranted_2_T_1 = firrtl.node %9 : !firrtl.uint<1>
  firrtl.strictconnect %notGranted_2, %_notGranted_2_T_1 : !firrtl.uint<1>
  %10 = firrtl.cat %grant_2, %grant_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %io_grant_hi = firrtl.node %10 : !firrtl.uint<2>
  %11 = firrtl.cat %io_grant_hi, %grant_0 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<3>
  %_io_grant_T = firrtl.node %11 : !firrtl.uint<3>
  firrtl.strictconnect %io_grant_1, %_io_grant_T : !firrtl.uint<3>
}

