// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @BasicPrefixAdder(in %clock1: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_a: !firrtl.uint<32>, in %io_b: !firrtl.uint<32>, in %io_cin: !firrtl.uint<1>, out %io_c: !firrtl.uint<32>, out %io_cout: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
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
  %16 = firrtl.and %io_a_0, %io_b_1 : (!firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %g = firrtl.node %16 : !firrtl.uint<32>
  %17 = firrtl.or %io_a_0, %io_b_1 : (!firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %a = firrtl.node %17 : !firrtl.uint<32>
  %18 = firrtl.xor %io_a_0, %io_b_1 : (!firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %p = firrtl.node %18 : !firrtl.uint<32>
  %res_g = firrtl.wire : !firrtl.uint<1>
  %res_a = firrtl.wire : !firrtl.uint<1>
  %19 = firrtl.bits %g 0 to 0 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T = firrtl.node %19 : !firrtl.uint<1>
  firrtl.strictconnect %res_g, %_res_g_T : !firrtl.uint<1>
  %20 = firrtl.bits %a 0 to 0 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T = firrtl.node %20 : !firrtl.uint<1>
  firrtl.strictconnect %res_a, %_res_a_T : !firrtl.uint<1>
  %res_1_g = firrtl.wire : !firrtl.uint<1>
  %res_1_a = firrtl.wire : !firrtl.uint<1>
  %21 = firrtl.bits %g 1 to 1 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_1 = firrtl.node %21 : !firrtl.uint<1>
  firrtl.strictconnect %res_1_g, %_res_g_T_1 : !firrtl.uint<1>
  %22 = firrtl.bits %a 1 to 1 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_1 = firrtl.node %22 : !firrtl.uint<1>
  firrtl.strictconnect %res_1_a, %_res_a_T_1 : !firrtl.uint<1>
  %res_2_g = firrtl.wire : !firrtl.uint<1>
  %res_2_a = firrtl.wire : !firrtl.uint<1>
  %23 = firrtl.bits %g 2 to 2 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_2 = firrtl.node %23 : !firrtl.uint<1>
  firrtl.strictconnect %res_2_g, %_res_g_T_2 : !firrtl.uint<1>
  %24 = firrtl.bits %a 2 to 2 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_2 = firrtl.node %24 : !firrtl.uint<1>
  firrtl.strictconnect %res_2_a, %_res_a_T_2 : !firrtl.uint<1>
  %res_3_g = firrtl.wire : !firrtl.uint<1>
  %res_3_a = firrtl.wire : !firrtl.uint<1>
  %25 = firrtl.bits %g 3 to 3 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_3 = firrtl.node %25 : !firrtl.uint<1>
  firrtl.strictconnect %res_3_g, %_res_g_T_3 : !firrtl.uint<1>
  %26 = firrtl.bits %a 3 to 3 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_3 = firrtl.node %26 : !firrtl.uint<1>
  firrtl.strictconnect %res_3_a, %_res_a_T_3 : !firrtl.uint<1>
  %res_4_g = firrtl.wire : !firrtl.uint<1>
  %res_4_a = firrtl.wire : !firrtl.uint<1>
  %27 = firrtl.bits %g 4 to 4 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_4 = firrtl.node %27 : !firrtl.uint<1>
  firrtl.strictconnect %res_4_g, %_res_g_T_4 : !firrtl.uint<1>
  %28 = firrtl.bits %a 4 to 4 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_4 = firrtl.node %28 : !firrtl.uint<1>
  firrtl.strictconnect %res_4_a, %_res_a_T_4 : !firrtl.uint<1>
  %res_5_g = firrtl.wire : !firrtl.uint<1>
  %res_5_a = firrtl.wire : !firrtl.uint<1>
  %29 = firrtl.bits %g 5 to 5 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_5 = firrtl.node %29 : !firrtl.uint<1>
  firrtl.strictconnect %res_5_g, %_res_g_T_5 : !firrtl.uint<1>
  %30 = firrtl.bits %a 5 to 5 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_5 = firrtl.node %30 : !firrtl.uint<1>
  firrtl.strictconnect %res_5_a, %_res_a_T_5 : !firrtl.uint<1>
  %res_6_g = firrtl.wire : !firrtl.uint<1>
  %res_6_a = firrtl.wire : !firrtl.uint<1>
  %31 = firrtl.bits %g 6 to 6 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_6 = firrtl.node %31 : !firrtl.uint<1>
  firrtl.strictconnect %res_6_g, %_res_g_T_6 : !firrtl.uint<1>
  %32 = firrtl.bits %a 6 to 6 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_6 = firrtl.node %32 : !firrtl.uint<1>
  firrtl.strictconnect %res_6_a, %_res_a_T_6 : !firrtl.uint<1>
  %res_7_g = firrtl.wire : !firrtl.uint<1>
  %res_7_a = firrtl.wire : !firrtl.uint<1>
  %33 = firrtl.bits %g 7 to 7 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_7 = firrtl.node %33 : !firrtl.uint<1>
  firrtl.strictconnect %res_7_g, %_res_g_T_7 : !firrtl.uint<1>
  %34 = firrtl.bits %a 7 to 7 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_7 = firrtl.node %34 : !firrtl.uint<1>
  firrtl.strictconnect %res_7_a, %_res_a_T_7 : !firrtl.uint<1>
  %res_8_g = firrtl.wire : !firrtl.uint<1>
  %res_8_a = firrtl.wire : !firrtl.uint<1>
  %35 = firrtl.bits %g 8 to 8 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_8 = firrtl.node %35 : !firrtl.uint<1>
  firrtl.strictconnect %res_8_g, %_res_g_T_8 : !firrtl.uint<1>
  %36 = firrtl.bits %a 8 to 8 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_8 = firrtl.node %36 : !firrtl.uint<1>
  firrtl.strictconnect %res_8_a, %_res_a_T_8 : !firrtl.uint<1>
  %res_9_g = firrtl.wire : !firrtl.uint<1>
  %res_9_a = firrtl.wire : !firrtl.uint<1>
  %37 = firrtl.bits %g 9 to 9 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_9 = firrtl.node %37 : !firrtl.uint<1>
  firrtl.strictconnect %res_9_g, %_res_g_T_9 : !firrtl.uint<1>
  %38 = firrtl.bits %a 9 to 9 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_9 = firrtl.node %38 : !firrtl.uint<1>
  firrtl.strictconnect %res_9_a, %_res_a_T_9 : !firrtl.uint<1>
  %res_10_g = firrtl.wire : !firrtl.uint<1>
  %res_10_a = firrtl.wire : !firrtl.uint<1>
  %39 = firrtl.bits %g 10 to 10 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_10 = firrtl.node %39 : !firrtl.uint<1>
  firrtl.strictconnect %res_10_g, %_res_g_T_10 : !firrtl.uint<1>
  %40 = firrtl.bits %a 10 to 10 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_10 = firrtl.node %40 : !firrtl.uint<1>
  firrtl.strictconnect %res_10_a, %_res_a_T_10 : !firrtl.uint<1>
  %res_11_g = firrtl.wire : !firrtl.uint<1>
  %res_11_a = firrtl.wire : !firrtl.uint<1>
  %41 = firrtl.bits %g 11 to 11 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_11 = firrtl.node %41 : !firrtl.uint<1>
  firrtl.strictconnect %res_11_g, %_res_g_T_11 : !firrtl.uint<1>
  %42 = firrtl.bits %a 11 to 11 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_11 = firrtl.node %42 : !firrtl.uint<1>
  firrtl.strictconnect %res_11_a, %_res_a_T_11 : !firrtl.uint<1>
  %res_12_g = firrtl.wire : !firrtl.uint<1>
  %res_12_a = firrtl.wire : !firrtl.uint<1>
  %43 = firrtl.bits %g 12 to 12 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_12 = firrtl.node %43 : !firrtl.uint<1>
  firrtl.strictconnect %res_12_g, %_res_g_T_12 : !firrtl.uint<1>
  %44 = firrtl.bits %a 12 to 12 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_12 = firrtl.node %44 : !firrtl.uint<1>
  firrtl.strictconnect %res_12_a, %_res_a_T_12 : !firrtl.uint<1>
  %res_13_g = firrtl.wire : !firrtl.uint<1>
  %res_13_a = firrtl.wire : !firrtl.uint<1>
  %45 = firrtl.bits %g 13 to 13 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_13 = firrtl.node %45 : !firrtl.uint<1>
  firrtl.strictconnect %res_13_g, %_res_g_T_13 : !firrtl.uint<1>
  %46 = firrtl.bits %a 13 to 13 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_13 = firrtl.node %46 : !firrtl.uint<1>
  firrtl.strictconnect %res_13_a, %_res_a_T_13 : !firrtl.uint<1>
  %res_14_g = firrtl.wire : !firrtl.uint<1>
  %res_14_a = firrtl.wire : !firrtl.uint<1>
  %47 = firrtl.bits %g 14 to 14 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_14 = firrtl.node %47 : !firrtl.uint<1>
  firrtl.strictconnect %res_14_g, %_res_g_T_14 : !firrtl.uint<1>
  %48 = firrtl.bits %a 14 to 14 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_14 = firrtl.node %48 : !firrtl.uint<1>
  firrtl.strictconnect %res_14_a, %_res_a_T_14 : !firrtl.uint<1>
  %res_15_g = firrtl.wire : !firrtl.uint<1>
  %res_15_a = firrtl.wire : !firrtl.uint<1>
  %49 = firrtl.bits %g 15 to 15 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_15 = firrtl.node %49 : !firrtl.uint<1>
  firrtl.strictconnect %res_15_g, %_res_g_T_15 : !firrtl.uint<1>
  %50 = firrtl.bits %a 15 to 15 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_15 = firrtl.node %50 : !firrtl.uint<1>
  firrtl.strictconnect %res_15_a, %_res_a_T_15 : !firrtl.uint<1>
  %res_16_g = firrtl.wire : !firrtl.uint<1>
  %res_16_a = firrtl.wire : !firrtl.uint<1>
  %51 = firrtl.bits %g 16 to 16 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_16 = firrtl.node %51 : !firrtl.uint<1>
  firrtl.strictconnect %res_16_g, %_res_g_T_16 : !firrtl.uint<1>
  %52 = firrtl.bits %a 16 to 16 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_16 = firrtl.node %52 : !firrtl.uint<1>
  firrtl.strictconnect %res_16_a, %_res_a_T_16 : !firrtl.uint<1>
  %res_17_g = firrtl.wire : !firrtl.uint<1>
  %res_17_a = firrtl.wire : !firrtl.uint<1>
  %53 = firrtl.bits %g 17 to 17 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_17 = firrtl.node %53 : !firrtl.uint<1>
  firrtl.strictconnect %res_17_g, %_res_g_T_17 : !firrtl.uint<1>
  %54 = firrtl.bits %a 17 to 17 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_17 = firrtl.node %54 : !firrtl.uint<1>
  firrtl.strictconnect %res_17_a, %_res_a_T_17 : !firrtl.uint<1>
  %res_18_g = firrtl.wire : !firrtl.uint<1>
  %res_18_a = firrtl.wire : !firrtl.uint<1>
  %55 = firrtl.bits %g 18 to 18 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_18 = firrtl.node %55 : !firrtl.uint<1>
  firrtl.strictconnect %res_18_g, %_res_g_T_18 : !firrtl.uint<1>
  %56 = firrtl.bits %a 18 to 18 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_18 = firrtl.node %56 : !firrtl.uint<1>
  firrtl.strictconnect %res_18_a, %_res_a_T_18 : !firrtl.uint<1>
  %res_19_g = firrtl.wire : !firrtl.uint<1>
  %res_19_a = firrtl.wire : !firrtl.uint<1>
  %57 = firrtl.bits %g 19 to 19 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_19 = firrtl.node %57 : !firrtl.uint<1>
  firrtl.strictconnect %res_19_g, %_res_g_T_19 : !firrtl.uint<1>
  %58 = firrtl.bits %a 19 to 19 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_19 = firrtl.node %58 : !firrtl.uint<1>
  firrtl.strictconnect %res_19_a, %_res_a_T_19 : !firrtl.uint<1>
  %res_20_g = firrtl.wire : !firrtl.uint<1>
  %res_20_a = firrtl.wire : !firrtl.uint<1>
  %59 = firrtl.bits %g 20 to 20 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_20 = firrtl.node %59 : !firrtl.uint<1>
  firrtl.strictconnect %res_20_g, %_res_g_T_20 : !firrtl.uint<1>
  %60 = firrtl.bits %a 20 to 20 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_20 = firrtl.node %60 : !firrtl.uint<1>
  firrtl.strictconnect %res_20_a, %_res_a_T_20 : !firrtl.uint<1>
  %res_21_g = firrtl.wire : !firrtl.uint<1>
  %res_21_a = firrtl.wire : !firrtl.uint<1>
  %61 = firrtl.bits %g 21 to 21 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_21 = firrtl.node %61 : !firrtl.uint<1>
  firrtl.strictconnect %res_21_g, %_res_g_T_21 : !firrtl.uint<1>
  %62 = firrtl.bits %a 21 to 21 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_21 = firrtl.node %62 : !firrtl.uint<1>
  firrtl.strictconnect %res_21_a, %_res_a_T_21 : !firrtl.uint<1>
  %res_22_g = firrtl.wire : !firrtl.uint<1>
  %res_22_a = firrtl.wire : !firrtl.uint<1>
  %63 = firrtl.bits %g 22 to 22 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_22 = firrtl.node %63 : !firrtl.uint<1>
  firrtl.strictconnect %res_22_g, %_res_g_T_22 : !firrtl.uint<1>
  %64 = firrtl.bits %a 22 to 22 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_22 = firrtl.node %64 : !firrtl.uint<1>
  firrtl.strictconnect %res_22_a, %_res_a_T_22 : !firrtl.uint<1>
  %res_23_g = firrtl.wire : !firrtl.uint<1>
  %res_23_a = firrtl.wire : !firrtl.uint<1>
  %65 = firrtl.bits %g 23 to 23 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_23 = firrtl.node %65 : !firrtl.uint<1>
  firrtl.strictconnect %res_23_g, %_res_g_T_23 : !firrtl.uint<1>
  %66 = firrtl.bits %a 23 to 23 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_23 = firrtl.node %66 : !firrtl.uint<1>
  firrtl.strictconnect %res_23_a, %_res_a_T_23 : !firrtl.uint<1>
  %res_24_g = firrtl.wire : !firrtl.uint<1>
  %res_24_a = firrtl.wire : !firrtl.uint<1>
  %67 = firrtl.bits %g 24 to 24 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_24 = firrtl.node %67 : !firrtl.uint<1>
  firrtl.strictconnect %res_24_g, %_res_g_T_24 : !firrtl.uint<1>
  %68 = firrtl.bits %a 24 to 24 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_24 = firrtl.node %68 : !firrtl.uint<1>
  firrtl.strictconnect %res_24_a, %_res_a_T_24 : !firrtl.uint<1>
  %res_25_g = firrtl.wire : !firrtl.uint<1>
  %res_25_a = firrtl.wire : !firrtl.uint<1>
  %69 = firrtl.bits %g 25 to 25 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_25 = firrtl.node %69 : !firrtl.uint<1>
  firrtl.strictconnect %res_25_g, %_res_g_T_25 : !firrtl.uint<1>
  %70 = firrtl.bits %a 25 to 25 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_25 = firrtl.node %70 : !firrtl.uint<1>
  firrtl.strictconnect %res_25_a, %_res_a_T_25 : !firrtl.uint<1>
  %res_26_g = firrtl.wire : !firrtl.uint<1>
  %res_26_a = firrtl.wire : !firrtl.uint<1>
  %71 = firrtl.bits %g 26 to 26 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_26 = firrtl.node %71 : !firrtl.uint<1>
  firrtl.strictconnect %res_26_g, %_res_g_T_26 : !firrtl.uint<1>
  %72 = firrtl.bits %a 26 to 26 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_26 = firrtl.node %72 : !firrtl.uint<1>
  firrtl.strictconnect %res_26_a, %_res_a_T_26 : !firrtl.uint<1>
  %res_27_g = firrtl.wire : !firrtl.uint<1>
  %res_27_a = firrtl.wire : !firrtl.uint<1>
  %73 = firrtl.bits %g 27 to 27 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_27 = firrtl.node %73 : !firrtl.uint<1>
  firrtl.strictconnect %res_27_g, %_res_g_T_27 : !firrtl.uint<1>
  %74 = firrtl.bits %a 27 to 27 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_27 = firrtl.node %74 : !firrtl.uint<1>
  firrtl.strictconnect %res_27_a, %_res_a_T_27 : !firrtl.uint<1>
  %res_28_g = firrtl.wire : !firrtl.uint<1>
  %res_28_a = firrtl.wire : !firrtl.uint<1>
  %75 = firrtl.bits %g 28 to 28 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_28 = firrtl.node %75 : !firrtl.uint<1>
  firrtl.strictconnect %res_28_g, %_res_g_T_28 : !firrtl.uint<1>
  %76 = firrtl.bits %a 28 to 28 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_28 = firrtl.node %76 : !firrtl.uint<1>
  firrtl.strictconnect %res_28_a, %_res_a_T_28 : !firrtl.uint<1>
  %res_29_g = firrtl.wire : !firrtl.uint<1>
  %res_29_a = firrtl.wire : !firrtl.uint<1>
  %77 = firrtl.bits %g 29 to 29 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_29 = firrtl.node %77 : !firrtl.uint<1>
  firrtl.strictconnect %res_29_g, %_res_g_T_29 : !firrtl.uint<1>
  %78 = firrtl.bits %a 29 to 29 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_29 = firrtl.node %78 : !firrtl.uint<1>
  firrtl.strictconnect %res_29_a, %_res_a_T_29 : !firrtl.uint<1>
  %res_30_g = firrtl.wire : !firrtl.uint<1>
  %res_30_a = firrtl.wire : !firrtl.uint<1>
  %79 = firrtl.bits %g 30 to 30 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_30 = firrtl.node %79 : !firrtl.uint<1>
  firrtl.strictconnect %res_30_g, %_res_g_T_30 : !firrtl.uint<1>
  %80 = firrtl.bits %a 30 to 30 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_30 = firrtl.node %80 : !firrtl.uint<1>
  firrtl.strictconnect %res_30_a, %_res_a_T_30 : !firrtl.uint<1>
  %res_31_g = firrtl.wire : !firrtl.uint<1>
  %res_31_a = firrtl.wire : !firrtl.uint<1>
  %81 = firrtl.bits %g 31 to 31 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_g_T_31 = firrtl.node %81 : !firrtl.uint<1>
  firrtl.strictconnect %res_31_g, %_res_g_T_31 : !firrtl.uint<1>
  %82 = firrtl.bits %a 31 to 31 : (!firrtl.uint<32>) -> !firrtl.uint<1>
  %_res_a_T_31 = firrtl.node %82 : !firrtl.uint<1>
  firrtl.strictconnect %res_31_a, %_res_a_T_31 : !firrtl.uint<1>
  %83 = firrtl.and %res_a, %io_cin_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %84 = firrtl.node %83 : !firrtl.uint<1>
  %85 = firrtl.or %res_g, %84 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %86 = firrtl.node %85 : !firrtl.uint<1>
  %res_32_g = firrtl.wire : !firrtl.uint<1>
  %res_32_a = firrtl.wire : !firrtl.uint<1>
  %87 = firrtl.and %res_2_a, %res_1_g : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_32 = firrtl.node %87 : !firrtl.uint<1>
  %88 = firrtl.or %res_2_g, %_res_g_T_32 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_33 = firrtl.node %88 : !firrtl.uint<1>
  firrtl.strictconnect %res_32_g, %_res_g_T_33 : !firrtl.uint<1>
  %89 = firrtl.and %res_2_a, %res_1_a : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_a_T_32 = firrtl.node %89 : !firrtl.uint<1>
  firrtl.strictconnect %res_32_a, %_res_a_T_32 : !firrtl.uint<1>
  %res_33_g = firrtl.wire : !firrtl.uint<1>
  %res_33_a = firrtl.wire : !firrtl.uint<1>
  %90 = firrtl.and %res_4_a, %res_3_g : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_34 = firrtl.node %90 : !firrtl.uint<1>
  %91 = firrtl.or %res_4_g, %_res_g_T_34 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_35 = firrtl.node %91 : !firrtl.uint<1>
  firrtl.strictconnect %res_33_g, %_res_g_T_35 : !firrtl.uint<1>
  %92 = firrtl.and %res_4_a, %res_3_a : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_a_T_33 = firrtl.node %92 : !firrtl.uint<1>
  firrtl.strictconnect %res_33_a, %_res_a_T_33 : !firrtl.uint<1>
  %res_34_g = firrtl.wire : !firrtl.uint<1>
  %res_34_a = firrtl.wire : !firrtl.uint<1>
  %93 = firrtl.and %res_6_a, %res_5_g : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_36 = firrtl.node %93 : !firrtl.uint<1>
  %94 = firrtl.or %res_6_g, %_res_g_T_36 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_37 = firrtl.node %94 : !firrtl.uint<1>
  firrtl.strictconnect %res_34_g, %_res_g_T_37 : !firrtl.uint<1>
  %95 = firrtl.and %res_6_a, %res_5_a : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_a_T_34 = firrtl.node %95 : !firrtl.uint<1>
  firrtl.strictconnect %res_34_a, %_res_a_T_34 : !firrtl.uint<1>
  %res_35_g = firrtl.wire : !firrtl.uint<1>
  %res_35_a = firrtl.wire : !firrtl.uint<1>
  %96 = firrtl.and %res_8_a, %res_7_g : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_38 = firrtl.node %96 : !firrtl.uint<1>
  %97 = firrtl.or %res_8_g, %_res_g_T_38 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_39 = firrtl.node %97 : !firrtl.uint<1>
  firrtl.strictconnect %res_35_g, %_res_g_T_39 : !firrtl.uint<1>
  %98 = firrtl.and %res_8_a, %res_7_a : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_a_T_35 = firrtl.node %98 : !firrtl.uint<1>
  firrtl.strictconnect %res_35_a, %_res_a_T_35 : !firrtl.uint<1>
  %res_36_g = firrtl.wire : !firrtl.uint<1>
  %res_36_a = firrtl.wire : !firrtl.uint<1>
  %99 = firrtl.and %res_10_a, %res_9_g : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_40 = firrtl.node %99 : !firrtl.uint<1>
  %100 = firrtl.or %res_10_g, %_res_g_T_40 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_41 = firrtl.node %100 : !firrtl.uint<1>
  firrtl.strictconnect %res_36_g, %_res_g_T_41 : !firrtl.uint<1>
  %101 = firrtl.and %res_10_a, %res_9_a : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_a_T_36 = firrtl.node %101 : !firrtl.uint<1>
  firrtl.strictconnect %res_36_a, %_res_a_T_36 : !firrtl.uint<1>
  %res_37_g = firrtl.wire : !firrtl.uint<1>
  %res_37_a = firrtl.wire : !firrtl.uint<1>
  %102 = firrtl.and %res_12_a, %res_11_g : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_42 = firrtl.node %102 : !firrtl.uint<1>
  %103 = firrtl.or %res_12_g, %_res_g_T_42 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_43 = firrtl.node %103 : !firrtl.uint<1>
  firrtl.strictconnect %res_37_g, %_res_g_T_43 : !firrtl.uint<1>
  %104 = firrtl.and %res_12_a, %res_11_a : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_a_T_37 = firrtl.node %104 : !firrtl.uint<1>
  firrtl.strictconnect %res_37_a, %_res_a_T_37 : !firrtl.uint<1>
  %res_38_g = firrtl.wire : !firrtl.uint<1>
  %res_38_a = firrtl.wire : !firrtl.uint<1>
  %105 = firrtl.and %res_14_a, %res_13_g : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_44 = firrtl.node %105 : !firrtl.uint<1>
  %106 = firrtl.or %res_14_g, %_res_g_T_44 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_45 = firrtl.node %106 : !firrtl.uint<1>
  firrtl.strictconnect %res_38_g, %_res_g_T_45 : !firrtl.uint<1>
  %107 = firrtl.and %res_14_a, %res_13_a : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_a_T_38 = firrtl.node %107 : !firrtl.uint<1>
  firrtl.strictconnect %res_38_a, %_res_a_T_38 : !firrtl.uint<1>
  %res_39_g = firrtl.wire : !firrtl.uint<1>
  %res_39_a = firrtl.wire : !firrtl.uint<1>
  %108 = firrtl.and %res_16_a, %res_15_g : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_46 = firrtl.node %108 : !firrtl.uint<1>
  %109 = firrtl.or %res_16_g, %_res_g_T_46 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_47 = firrtl.node %109 : !firrtl.uint<1>
  firrtl.strictconnect %res_39_g, %_res_g_T_47 : !firrtl.uint<1>
  %110 = firrtl.and %res_16_a, %res_15_a : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_a_T_39 = firrtl.node %110 : !firrtl.uint<1>
  firrtl.strictconnect %res_39_a, %_res_a_T_39 : !firrtl.uint<1>
  %res_40_g = firrtl.wire : !firrtl.uint<1>
  %res_40_a = firrtl.wire : !firrtl.uint<1>
  %111 = firrtl.and %res_18_a, %res_17_g : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_48 = firrtl.node %111 : !firrtl.uint<1>
  %112 = firrtl.or %res_18_g, %_res_g_T_48 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_49 = firrtl.node %112 : !firrtl.uint<1>
  firrtl.strictconnect %res_40_g, %_res_g_T_49 : !firrtl.uint<1>
  %113 = firrtl.and %res_18_a, %res_17_a : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_a_T_40 = firrtl.node %113 : !firrtl.uint<1>
  firrtl.strictconnect %res_40_a, %_res_a_T_40 : !firrtl.uint<1>
  %res_41_g = firrtl.wire : !firrtl.uint<1>
  %res_41_a = firrtl.wire : !firrtl.uint<1>
  %114 = firrtl.and %res_20_a, %res_19_g : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_50 = firrtl.node %114 : !firrtl.uint<1>
  %115 = firrtl.or %res_20_g, %_res_g_T_50 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_51 = firrtl.node %115 : !firrtl.uint<1>
  firrtl.strictconnect %res_41_g, %_res_g_T_51 : !firrtl.uint<1>
  %116 = firrtl.and %res_20_a, %res_19_a : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_a_T_41 = firrtl.node %116 : !firrtl.uint<1>
  firrtl.strictconnect %res_41_a, %_res_a_T_41 : !firrtl.uint<1>
  %res_42_g = firrtl.wire : !firrtl.uint<1>
  %res_42_a = firrtl.wire : !firrtl.uint<1>
  %117 = firrtl.and %res_22_a, %res_21_g : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_52 = firrtl.node %117 : !firrtl.uint<1>
  %118 = firrtl.or %res_22_g, %_res_g_T_52 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_53 = firrtl.node %118 : !firrtl.uint<1>
  firrtl.strictconnect %res_42_g, %_res_g_T_53 : !firrtl.uint<1>
  %119 = firrtl.and %res_22_a, %res_21_a : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_a_T_42 = firrtl.node %119 : !firrtl.uint<1>
  firrtl.strictconnect %res_42_a, %_res_a_T_42 : !firrtl.uint<1>
  %res_43_g = firrtl.wire : !firrtl.uint<1>
  %res_43_a = firrtl.wire : !firrtl.uint<1>
  %120 = firrtl.and %res_24_a, %res_23_g : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_54 = firrtl.node %120 : !firrtl.uint<1>
  %121 = firrtl.or %res_24_g, %_res_g_T_54 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_55 = firrtl.node %121 : !firrtl.uint<1>
  firrtl.strictconnect %res_43_g, %_res_g_T_55 : !firrtl.uint<1>
  %122 = firrtl.and %res_24_a, %res_23_a : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_a_T_43 = firrtl.node %122 : !firrtl.uint<1>
  firrtl.strictconnect %res_43_a, %_res_a_T_43 : !firrtl.uint<1>
  %res_44_g = firrtl.wire : !firrtl.uint<1>
  %res_44_a = firrtl.wire : !firrtl.uint<1>
  %123 = firrtl.and %res_26_a, %res_25_g : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_56 = firrtl.node %123 : !firrtl.uint<1>
  %124 = firrtl.or %res_26_g, %_res_g_T_56 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_57 = firrtl.node %124 : !firrtl.uint<1>
  firrtl.strictconnect %res_44_g, %_res_g_T_57 : !firrtl.uint<1>
  %125 = firrtl.and %res_26_a, %res_25_a : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_a_T_44 = firrtl.node %125 : !firrtl.uint<1>
  firrtl.strictconnect %res_44_a, %_res_a_T_44 : !firrtl.uint<1>
  %res_45_g = firrtl.wire : !firrtl.uint<1>
  %res_45_a = firrtl.wire : !firrtl.uint<1>
  %126 = firrtl.and %res_28_a, %res_27_g : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_58 = firrtl.node %126 : !firrtl.uint<1>
  %127 = firrtl.or %res_28_g, %_res_g_T_58 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_59 = firrtl.node %127 : !firrtl.uint<1>
  firrtl.strictconnect %res_45_g, %_res_g_T_59 : !firrtl.uint<1>
  %128 = firrtl.and %res_28_a, %res_27_a : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_a_T_45 = firrtl.node %128 : !firrtl.uint<1>
  firrtl.strictconnect %res_45_a, %_res_a_T_45 : !firrtl.uint<1>
  %res_46_g = firrtl.wire : !firrtl.uint<1>
  %res_46_a = firrtl.wire : !firrtl.uint<1>
  %129 = firrtl.and %res_30_a, %res_29_g : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_60 = firrtl.node %129 : !firrtl.uint<1>
  %130 = firrtl.or %res_30_g, %_res_g_T_60 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_g_T_61 = firrtl.node %130 : !firrtl.uint<1>
  firrtl.strictconnect %res_46_g, %_res_g_T_61 : !firrtl.uint<1>
  %131 = firrtl.and %res_30_a, %res_29_a : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_res_a_T_46 = firrtl.node %131 : !firrtl.uint<1>
  firrtl.strictconnect %res_46_a, %_res_a_T_46 : !firrtl.uint<1>
  %132 = firrtl.and %res_1_a, %86 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %133 = firrtl.node %132 : !firrtl.uint<1>
  %134 = firrtl.or %res_1_g, %133 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %135 = firrtl.node %134 : !firrtl.uint<1>
  %136 = firrtl.and %res_32_a, %86 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %137 = firrtl.node %136 : !firrtl.uint<1>
  %138 = firrtl.or %res_32_g, %137 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %139 = firrtl.node %138 : !firrtl.uint<1>
  %140 = firrtl.and %res_3_a, %139 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %141 = firrtl.node %140 : !firrtl.uint<1>
  %142 = firrtl.or %res_3_g, %141 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %143 = firrtl.node %142 : !firrtl.uint<1>
  %144 = firrtl.and %res_33_a, %139 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %145 = firrtl.node %144 : !firrtl.uint<1>
  %146 = firrtl.or %res_33_g, %145 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %147 = firrtl.node %146 : !firrtl.uint<1>
  %148 = firrtl.and %res_5_a, %147 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %149 = firrtl.node %148 : !firrtl.uint<1>
  %150 = firrtl.or %res_5_g, %149 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %151 = firrtl.node %150 : !firrtl.uint<1>
  %152 = firrtl.and %res_34_a, %147 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %153 = firrtl.node %152 : !firrtl.uint<1>
  %154 = firrtl.or %res_34_g, %153 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %155 = firrtl.node %154 : !firrtl.uint<1>
  %156 = firrtl.and %res_7_a, %155 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %157 = firrtl.node %156 : !firrtl.uint<1>
  %158 = firrtl.or %res_7_g, %157 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %159 = firrtl.node %158 : !firrtl.uint<1>
  %160 = firrtl.and %res_35_a, %155 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %161 = firrtl.node %160 : !firrtl.uint<1>
  %162 = firrtl.or %res_35_g, %161 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %163 = firrtl.node %162 : !firrtl.uint<1>
  %164 = firrtl.and %res_9_a, %163 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %165 = firrtl.node %164 : !firrtl.uint<1>
  %166 = firrtl.or %res_9_g, %165 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %167 = firrtl.node %166 : !firrtl.uint<1>
  %168 = firrtl.and %res_36_a, %163 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %169 = firrtl.node %168 : !firrtl.uint<1>
  %170 = firrtl.or %res_36_g, %169 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %171 = firrtl.node %170 : !firrtl.uint<1>
  %172 = firrtl.and %res_11_a, %171 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %173 = firrtl.node %172 : !firrtl.uint<1>
  %174 = firrtl.or %res_11_g, %173 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %175 = firrtl.node %174 : !firrtl.uint<1>
  %176 = firrtl.and %res_37_a, %171 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %177 = firrtl.node %176 : !firrtl.uint<1>
  %178 = firrtl.or %res_37_g, %177 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %179 = firrtl.node %178 : !firrtl.uint<1>
  %180 = firrtl.and %res_13_a, %179 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %181 = firrtl.node %180 : !firrtl.uint<1>
  %182 = firrtl.or %res_13_g, %181 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %183 = firrtl.node %182 : !firrtl.uint<1>
  %184 = firrtl.and %res_38_a, %179 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %185 = firrtl.node %184 : !firrtl.uint<1>
  %186 = firrtl.or %res_38_g, %185 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %187 = firrtl.node %186 : !firrtl.uint<1>
  %188 = firrtl.and %res_15_a, %187 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %189 = firrtl.node %188 : !firrtl.uint<1>
  %190 = firrtl.or %res_15_g, %189 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %191 = firrtl.node %190 : !firrtl.uint<1>
  %192 = firrtl.and %res_39_a, %187 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %193 = firrtl.node %192 : !firrtl.uint<1>
  %194 = firrtl.or %res_39_g, %193 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %195 = firrtl.node %194 : !firrtl.uint<1>
  %196 = firrtl.and %res_17_a, %195 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %197 = firrtl.node %196 : !firrtl.uint<1>
  %198 = firrtl.or %res_17_g, %197 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %199 = firrtl.node %198 : !firrtl.uint<1>
  %200 = firrtl.and %res_40_a, %195 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %201 = firrtl.node %200 : !firrtl.uint<1>
  %202 = firrtl.or %res_40_g, %201 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %203 = firrtl.node %202 : !firrtl.uint<1>
  %204 = firrtl.and %res_19_a, %203 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %205 = firrtl.node %204 : !firrtl.uint<1>
  %206 = firrtl.or %res_19_g, %205 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %207 = firrtl.node %206 : !firrtl.uint<1>
  %208 = firrtl.and %res_41_a, %203 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %209 = firrtl.node %208 : !firrtl.uint<1>
  %210 = firrtl.or %res_41_g, %209 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %211 = firrtl.node %210 : !firrtl.uint<1>
  %212 = firrtl.and %res_21_a, %211 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %213 = firrtl.node %212 : !firrtl.uint<1>
  %214 = firrtl.or %res_21_g, %213 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %215 = firrtl.node %214 : !firrtl.uint<1>
  %216 = firrtl.and %res_42_a, %211 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %217 = firrtl.node %216 : !firrtl.uint<1>
  %218 = firrtl.or %res_42_g, %217 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %219 = firrtl.node %218 : !firrtl.uint<1>
  %220 = firrtl.and %res_23_a, %219 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %221 = firrtl.node %220 : !firrtl.uint<1>
  %222 = firrtl.or %res_23_g, %221 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %223 = firrtl.node %222 : !firrtl.uint<1>
  %224 = firrtl.and %res_43_a, %219 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %225 = firrtl.node %224 : !firrtl.uint<1>
  %226 = firrtl.or %res_43_g, %225 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %227 = firrtl.node %226 : !firrtl.uint<1>
  %228 = firrtl.and %res_25_a, %227 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %229 = firrtl.node %228 : !firrtl.uint<1>
  %230 = firrtl.or %res_25_g, %229 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %231 = firrtl.node %230 : !firrtl.uint<1>
  %232 = firrtl.and %res_44_a, %227 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %233 = firrtl.node %232 : !firrtl.uint<1>
  %234 = firrtl.or %res_44_g, %233 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %235 = firrtl.node %234 : !firrtl.uint<1>
  %236 = firrtl.and %res_27_a, %235 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %237 = firrtl.node %236 : !firrtl.uint<1>
  %238 = firrtl.or %res_27_g, %237 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %239 = firrtl.node %238 : !firrtl.uint<1>
  %240 = firrtl.and %res_45_a, %235 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %241 = firrtl.node %240 : !firrtl.uint<1>
  %242 = firrtl.or %res_45_g, %241 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %243 = firrtl.node %242 : !firrtl.uint<1>
  %244 = firrtl.and %res_29_a, %243 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %245 = firrtl.node %244 : !firrtl.uint<1>
  %246 = firrtl.or %res_29_g, %245 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %247 = firrtl.node %246 : !firrtl.uint<1>
  %248 = firrtl.and %res_46_a, %243 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %249 = firrtl.node %248 : !firrtl.uint<1>
  %250 = firrtl.or %res_46_g, %249 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %251 = firrtl.node %250 : !firrtl.uint<1>
  %252 = firrtl.and %res_31_a, %251 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %253 = firrtl.node %252 : !firrtl.uint<1>
  %254 = firrtl.or %res_31_g, %253 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %255 = firrtl.node %254 : !firrtl.uint<1>
  %_cs_WIRE_0 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_1 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_2 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_3 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_4 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_5 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_6 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_7 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_8 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_9 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_10 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_11 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_12 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_13 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_14 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_15 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_16 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_17 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_18 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_19 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_20 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_21 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_22 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_23 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_24 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_25 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_26 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_27 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_28 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_29 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_30 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_31 = firrtl.wire : !firrtl.uint<1>
  %_cs_WIRE_32 = firrtl.wire : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_0, %io_cin_2 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_1, %86 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_2, %135 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_3, %139 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_4, %143 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_5, %147 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_6, %151 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_7, %155 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_8, %159 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_9, %163 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_10, %167 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_11, %171 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_12, %175 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_13, %179 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_14, %183 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_15, %187 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_16, %191 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_17, %195 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_18, %199 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_19, %203 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_20, %207 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_21, %211 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_22, %215 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_23, %219 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_24, %223 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_25, %227 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_26, %231 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_27, %235 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_28, %239 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_29, %243 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_30, %247 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_31, %251 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_32, %255 : !firrtl.uint<1>
  %256 = firrtl.cat %_cs_WIRE_1, %_cs_WIRE_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_lo_lo_lo_lo = firrtl.node %256 : !firrtl.uint<2>
  %257 = firrtl.cat %_cs_WIRE_3, %_cs_WIRE_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_lo_lo_lo_hi = firrtl.node %257 : !firrtl.uint<2>
  %258 = firrtl.cat %cs_lo_lo_lo_hi, %cs_lo_lo_lo_lo : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<4>
  %cs_lo_lo_lo = firrtl.node %258 : !firrtl.uint<4>
  %259 = firrtl.cat %_cs_WIRE_5, %_cs_WIRE_4 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_lo_lo_hi_lo = firrtl.node %259 : !firrtl.uint<2>
  %260 = firrtl.cat %_cs_WIRE_7, %_cs_WIRE_6 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_lo_lo_hi_hi = firrtl.node %260 : !firrtl.uint<2>
  %261 = firrtl.cat %cs_lo_lo_hi_hi, %cs_lo_lo_hi_lo : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<4>
  %cs_lo_lo_hi = firrtl.node %261 : !firrtl.uint<4>
  %262 = firrtl.cat %cs_lo_lo_hi, %cs_lo_lo_lo : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>
  %cs_lo_lo = firrtl.node %262 : !firrtl.uint<8>
  %263 = firrtl.cat %_cs_WIRE_9, %_cs_WIRE_8 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_lo_hi_lo_lo = firrtl.node %263 : !firrtl.uint<2>
  %264 = firrtl.cat %_cs_WIRE_11, %_cs_WIRE_10 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_lo_hi_lo_hi = firrtl.node %264 : !firrtl.uint<2>
  %265 = firrtl.cat %cs_lo_hi_lo_hi, %cs_lo_hi_lo_lo : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<4>
  %cs_lo_hi_lo = firrtl.node %265 : !firrtl.uint<4>
  %266 = firrtl.cat %_cs_WIRE_13, %_cs_WIRE_12 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_lo_hi_hi_lo = firrtl.node %266 : !firrtl.uint<2>
  %267 = firrtl.cat %_cs_WIRE_15, %_cs_WIRE_14 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_lo_hi_hi_hi = firrtl.node %267 : !firrtl.uint<2>
  %268 = firrtl.cat %cs_lo_hi_hi_hi, %cs_lo_hi_hi_lo : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<4>
  %cs_lo_hi_hi = firrtl.node %268 : !firrtl.uint<4>
  %269 = firrtl.cat %cs_lo_hi_hi, %cs_lo_hi_lo : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>
  %cs_lo_hi = firrtl.node %269 : !firrtl.uint<8>
  %270 = firrtl.cat %cs_lo_hi, %cs_lo_lo : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<16>
  %cs_lo = firrtl.node %270 : !firrtl.uint<16>
  %271 = firrtl.cat %_cs_WIRE_17, %_cs_WIRE_16 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_hi_lo_lo_lo = firrtl.node %271 : !firrtl.uint<2>
  %272 = firrtl.cat %_cs_WIRE_19, %_cs_WIRE_18 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_hi_lo_lo_hi = firrtl.node %272 : !firrtl.uint<2>
  %273 = firrtl.cat %cs_hi_lo_lo_hi, %cs_hi_lo_lo_lo : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<4>
  %cs_hi_lo_lo = firrtl.node %273 : !firrtl.uint<4>
  %274 = firrtl.cat %_cs_WIRE_21, %_cs_WIRE_20 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_hi_lo_hi_lo = firrtl.node %274 : !firrtl.uint<2>
  %275 = firrtl.cat %_cs_WIRE_23, %_cs_WIRE_22 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_hi_lo_hi_hi = firrtl.node %275 : !firrtl.uint<2>
  %276 = firrtl.cat %cs_hi_lo_hi_hi, %cs_hi_lo_hi_lo : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<4>
  %cs_hi_lo_hi = firrtl.node %276 : !firrtl.uint<4>
  %277 = firrtl.cat %cs_hi_lo_hi, %cs_hi_lo_lo : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>
  %cs_hi_lo = firrtl.node %277 : !firrtl.uint<8>
  %278 = firrtl.cat %_cs_WIRE_25, %_cs_WIRE_24 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_hi_hi_lo_lo = firrtl.node %278 : !firrtl.uint<2>
  %279 = firrtl.cat %_cs_WIRE_27, %_cs_WIRE_26 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_hi_hi_lo_hi = firrtl.node %279 : !firrtl.uint<2>
  %280 = firrtl.cat %cs_hi_hi_lo_hi, %cs_hi_hi_lo_lo : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<4>
  %cs_hi_hi_lo = firrtl.node %280 : !firrtl.uint<4>
  %281 = firrtl.cat %_cs_WIRE_29, %_cs_WIRE_28 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_hi_hi_hi_lo = firrtl.node %281 : !firrtl.uint<2>
  %282 = firrtl.cat %_cs_WIRE_32, %_cs_WIRE_31 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_hi_hi_hi_hi_hi = firrtl.node %282 : !firrtl.uint<2>
  %283 = firrtl.cat %cs_hi_hi_hi_hi_hi, %_cs_WIRE_30 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<3>
  %cs_hi_hi_hi_hi = firrtl.node %283 : !firrtl.uint<3>
  %284 = firrtl.cat %cs_hi_hi_hi_hi, %cs_hi_hi_hi_lo : (!firrtl.uint<3>, !firrtl.uint<2>) -> !firrtl.uint<5>
  %cs_hi_hi_hi = firrtl.node %284 : !firrtl.uint<5>
  %285 = firrtl.cat %cs_hi_hi_hi, %cs_hi_hi_lo : (!firrtl.uint<5>, !firrtl.uint<4>) -> !firrtl.uint<9>
  %cs_hi_hi = firrtl.node %285 : !firrtl.uint<9>
  %286 = firrtl.cat %cs_hi_hi, %cs_hi_lo : (!firrtl.uint<9>, !firrtl.uint<8>) -> !firrtl.uint<17>
  %cs_hi = firrtl.node %286 : !firrtl.uint<17>
  %287 = firrtl.cat %cs_hi, %cs_lo : (!firrtl.uint<17>, !firrtl.uint<16>) -> !firrtl.uint<33>
  %cs = firrtl.node %287 : !firrtl.uint<33>
  %288 = firrtl.bits %cs 31 to 0 : (!firrtl.uint<33>) -> !firrtl.uint<32>
  %_io_c_T = firrtl.node %288 : !firrtl.uint<32>
  %289 = firrtl.xor %p, %_io_c_T : (!firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %_io_c_T_1 = firrtl.node %289 : !firrtl.uint<32>
  firrtl.strictconnect %io_c_3, %_io_c_T_1 : !firrtl.uint<32>
  %290 = firrtl.bits %cs 32 to 32 : (!firrtl.uint<33>) -> !firrtl.uint<1>
  %_io_cout_T = firrtl.node %290 : !firrtl.uint<1>
  firrtl.strictconnect %io_cout_4, %_io_cout_T : !firrtl.uint<1>
}

