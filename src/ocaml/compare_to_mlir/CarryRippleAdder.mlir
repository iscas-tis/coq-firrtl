// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @CarryRippleAdder(in %clock1: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_a: !firrtl.uint<32>, in %io_b: !firrtl.uint<32>, in %io_cin: !firrtl.uint<1>, out %io_c: !firrtl.uint<32>, out %io_cout: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_a_0 = firrtl.wire {name = "io_a"} : !firrtl.uint<32>
  %io_b_1 = firrtl.wire {name = "io_b"} : !firrtl.uint<32>
  %io_cin_2 = firrtl.wire {name = "io_cin"} : !firrtl.uint<1>
  %io_c_3 = firrtl.wire {name = "io_c"} : !firrtl.uint<32>
  %io_cout_4 = firrtl.wire {name = "io_cout"} : !firrtl.uint<1>
  firrtl.strictconnect %io_a_0, %io_a : !firrtl.uint<32>
  firrtl.strictconnect %io_b_1, %io_b : !firrtl.uint<32>
  firrtl.strictconnect %io_cin_2, %io_cin : !firrtl.uint<1>
  firrtl.strictconnect %io_c, %io_c_3 : !firrtl.uint<32>
  firrtl.strictconnect %io_cout, %io_cout_4 : !firrtl.uint<1>
  %aOp_0 = firrtl.wire : !firrtl.uint<4>
  %aOp_1 = firrtl.wire : !firrtl.uint<4>
  %aOp_2 = firrtl.wire : !firrtl.uint<4>
  %aOp_3 = firrtl.wire : !firrtl.uint<4>
  %aOp_4 = firrtl.wire : !firrtl.uint<4>
  %aOp_5 = firrtl.wire : !firrtl.uint<4>
  %aOp_6 = firrtl.wire : !firrtl.uint<4>
  %aOp_7 = firrtl.wire : !firrtl.uint<4>
  %_aOp_WIRE = firrtl.wire : !firrtl.uint<32>
  firrtl.strictconnect %_aOp_WIRE, %io_a_0 : !firrtl.uint<32>
  %0 = firrtl.bits %_aOp_WIRE 3 to 0 : (!firrtl.uint<32>) -> !firrtl.uint<4>
  %_aOp_T = firrtl.node %0 : !firrtl.uint<4>
  firrtl.strictconnect %aOp_0, %_aOp_T : !firrtl.uint<4>
  %1 = firrtl.bits %_aOp_WIRE 7 to 4 : (!firrtl.uint<32>) -> !firrtl.uint<4>
  %_aOp_T_1 = firrtl.node %1 : !firrtl.uint<4>
  firrtl.strictconnect %aOp_1, %_aOp_T_1 : !firrtl.uint<4>
  %2 = firrtl.bits %_aOp_WIRE 11 to 8 : (!firrtl.uint<32>) -> !firrtl.uint<4>
  %_aOp_T_2 = firrtl.node %2 : !firrtl.uint<4>
  firrtl.strictconnect %aOp_2, %_aOp_T_2 : !firrtl.uint<4>
  %3 = firrtl.bits %_aOp_WIRE 15 to 12 : (!firrtl.uint<32>) -> !firrtl.uint<4>
  %_aOp_T_3 = firrtl.node %3 : !firrtl.uint<4>
  firrtl.strictconnect %aOp_3, %_aOp_T_3 : !firrtl.uint<4>
  %4 = firrtl.bits %_aOp_WIRE 19 to 16 : (!firrtl.uint<32>) -> !firrtl.uint<4>
  %_aOp_T_4 = firrtl.node %4 : !firrtl.uint<4>
  firrtl.strictconnect %aOp_4, %_aOp_T_4 : !firrtl.uint<4>
  %5 = firrtl.bits %_aOp_WIRE 23 to 20 : (!firrtl.uint<32>) -> !firrtl.uint<4>
  %_aOp_T_5 = firrtl.node %5 : !firrtl.uint<4>
  firrtl.strictconnect %aOp_5, %_aOp_T_5 : !firrtl.uint<4>
  %6 = firrtl.bits %_aOp_WIRE 27 to 24 : (!firrtl.uint<32>) -> !firrtl.uint<4>
  %_aOp_T_6 = firrtl.node %6 : !firrtl.uint<4>
  firrtl.strictconnect %aOp_6, %_aOp_T_6 : !firrtl.uint<4>
  %7 = firrtl.bits %_aOp_WIRE 31 to 28 : (!firrtl.uint<32>) -> !firrtl.uint<4>
  %_aOp_T_7 = firrtl.node %7 : !firrtl.uint<4>
  firrtl.strictconnect %aOp_7, %_aOp_T_7 : !firrtl.uint<4>
  %bOp_0 = firrtl.wire : !firrtl.uint<4>
  %bOp_1 = firrtl.wire : !firrtl.uint<4>
  %bOp_2 = firrtl.wire : !firrtl.uint<4>
  %bOp_3 = firrtl.wire : !firrtl.uint<4>
  %bOp_4 = firrtl.wire : !firrtl.uint<4>
  %bOp_5 = firrtl.wire : !firrtl.uint<4>
  %bOp_6 = firrtl.wire : !firrtl.uint<4>
  %bOp_7 = firrtl.wire : !firrtl.uint<4>
  %_bOp_WIRE = firrtl.wire : !firrtl.uint<32>
  firrtl.strictconnect %_bOp_WIRE, %io_b_1 : !firrtl.uint<32>
  %8 = firrtl.bits %_bOp_WIRE 3 to 0 : (!firrtl.uint<32>) -> !firrtl.uint<4>
  %_bOp_T = firrtl.node %8 : !firrtl.uint<4>
  firrtl.strictconnect %bOp_0, %_bOp_T : !firrtl.uint<4>
  %9 = firrtl.bits %_bOp_WIRE 7 to 4 : (!firrtl.uint<32>) -> !firrtl.uint<4>
  %_bOp_T_1 = firrtl.node %9 : !firrtl.uint<4>
  firrtl.strictconnect %bOp_1, %_bOp_T_1 : !firrtl.uint<4>
  %10 = firrtl.bits %_bOp_WIRE 11 to 8 : (!firrtl.uint<32>) -> !firrtl.uint<4>
  %_bOp_T_2 = firrtl.node %10 : !firrtl.uint<4>
  firrtl.strictconnect %bOp_2, %_bOp_T_2 : !firrtl.uint<4>
  %11 = firrtl.bits %_bOp_WIRE 15 to 12 : (!firrtl.uint<32>) -> !firrtl.uint<4>
  %_bOp_T_3 = firrtl.node %11 : !firrtl.uint<4>
  firrtl.strictconnect %bOp_3, %_bOp_T_3 : !firrtl.uint<4>
  %12 = firrtl.bits %_bOp_WIRE 19 to 16 : (!firrtl.uint<32>) -> !firrtl.uint<4>
  %_bOp_T_4 = firrtl.node %12 : !firrtl.uint<4>
  firrtl.strictconnect %bOp_4, %_bOp_T_4 : !firrtl.uint<4>
  %13 = firrtl.bits %_bOp_WIRE 23 to 20 : (!firrtl.uint<32>) -> !firrtl.uint<4>
  %_bOp_T_5 = firrtl.node %13 : !firrtl.uint<4>
  firrtl.strictconnect %bOp_5, %_bOp_T_5 : !firrtl.uint<4>
  %14 = firrtl.bits %_bOp_WIRE 27 to 24 : (!firrtl.uint<32>) -> !firrtl.uint<4>
  %_bOp_T_6 = firrtl.node %14 : !firrtl.uint<4>
  firrtl.strictconnect %bOp_6, %_bOp_T_6 : !firrtl.uint<4>
  %15 = firrtl.bits %_bOp_WIRE 31 to 28 : (!firrtl.uint<32>) -> !firrtl.uint<4>
  %_bOp_T_7 = firrtl.node %15 : !firrtl.uint<4>
  firrtl.strictconnect %bOp_7, %_bOp_T_7 : !firrtl.uint<4>
  %16 = firrtl.add %io_a_0, %io_b_1 : (!firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<33>
  %_res_T = firrtl.node %16 : !firrtl.uint<33>
  %17 = firrtl.add %_res_T, %io_cin_2 : (!firrtl.uint<33>, !firrtl.uint<1>) -> !firrtl.uint<34>
  %_res_T_1 = firrtl.node %17 : !firrtl.uint<34>
  %18 = firrtl.tail %_res_T_1, 1 : (!firrtl.uint<34>) -> !firrtl.uint<33>
  %res = firrtl.node %18 : !firrtl.uint<33>
  %19 = firrtl.bits %res 31 to 0 : (!firrtl.uint<33>) -> !firrtl.uint<32>
  %_io_c_T = firrtl.node %19 : !firrtl.uint<32>
  firrtl.strictconnect %io_c_3, %_io_c_T : !firrtl.uint<32>
  %20 = firrtl.bits %res 32 to 32 : (!firrtl.uint<33>) -> !firrtl.uint<1>
  %_io_cout_T = firrtl.node %20 : !firrtl.uint<1>
  firrtl.strictconnect %io_cout_4, %_io_cout_T : !firrtl.uint<1>
}

