// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @MinFanoutPrefixAdder(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %io_a: !firrtl.uint<32>, in %io_b: !firrtl.uint<32>, in %io_cin: !firrtl.uint<1>, out %io_c: !firrtl.uint<32>, out %io_cout: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
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
  %87 = firrtl.and %res_1_a, %86 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %88 = firrtl.node %87 : !firrtl.uint<1>
  %89 = firrtl.or %res_1_g, %88 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %90 = firrtl.node %89 : !firrtl.uint<1>
  %91 = firrtl.and %res_2_a, %90 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %92 = firrtl.node %91 : !firrtl.uint<1>
  %93 = firrtl.or %res_2_g, %92 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %94 = firrtl.node %93 : !firrtl.uint<1>
  %95 = firrtl.and %res_3_a, %94 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %96 = firrtl.node %95 : !firrtl.uint<1>
  %97 = firrtl.or %res_3_g, %96 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %98 = firrtl.node %97 : !firrtl.uint<1>
  %99 = firrtl.and %res_4_a, %98 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %100 = firrtl.node %99 : !firrtl.uint<1>
  %101 = firrtl.or %res_4_g, %100 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %102 = firrtl.node %101 : !firrtl.uint<1>
  %103 = firrtl.and %res_5_a, %102 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %104 = firrtl.node %103 : !firrtl.uint<1>
  %105 = firrtl.or %res_5_g, %104 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %106 = firrtl.node %105 : !firrtl.uint<1>
  %107 = firrtl.and %res_6_a, %106 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %108 = firrtl.node %107 : !firrtl.uint<1>
  %109 = firrtl.or %res_6_g, %108 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %110 = firrtl.node %109 : !firrtl.uint<1>
  %111 = firrtl.and %res_7_a, %110 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %112 = firrtl.node %111 : !firrtl.uint<1>
  %113 = firrtl.or %res_7_g, %112 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %114 = firrtl.node %113 : !firrtl.uint<1>
  %115 = firrtl.and %res_8_a, %114 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %116 = firrtl.node %115 : !firrtl.uint<1>
  %117 = firrtl.or %res_8_g, %116 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %118 = firrtl.node %117 : !firrtl.uint<1>
  %119 = firrtl.and %res_9_a, %118 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %120 = firrtl.node %119 : !firrtl.uint<1>
  %121 = firrtl.or %res_9_g, %120 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %122 = firrtl.node %121 : !firrtl.uint<1>
  %123 = firrtl.and %res_10_a, %122 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %124 = firrtl.node %123 : !firrtl.uint<1>
  %125 = firrtl.or %res_10_g, %124 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %126 = firrtl.node %125 : !firrtl.uint<1>
  %127 = firrtl.and %res_11_a, %126 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %128 = firrtl.node %127 : !firrtl.uint<1>
  %129 = firrtl.or %res_11_g, %128 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %130 = firrtl.node %129 : !firrtl.uint<1>
  %131 = firrtl.and %res_12_a, %130 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %132 = firrtl.node %131 : !firrtl.uint<1>
  %133 = firrtl.or %res_12_g, %132 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %134 = firrtl.node %133 : !firrtl.uint<1>
  %135 = firrtl.and %res_13_a, %134 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %136 = firrtl.node %135 : !firrtl.uint<1>
  %137 = firrtl.or %res_13_g, %136 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %138 = firrtl.node %137 : !firrtl.uint<1>
  %139 = firrtl.and %res_14_a, %138 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %140 = firrtl.node %139 : !firrtl.uint<1>
  %141 = firrtl.or %res_14_g, %140 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %142 = firrtl.node %141 : !firrtl.uint<1>
  %143 = firrtl.and %res_15_a, %142 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %144 = firrtl.node %143 : !firrtl.uint<1>
  %145 = firrtl.or %res_15_g, %144 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %146 = firrtl.node %145 : !firrtl.uint<1>
  %147 = firrtl.and %res_16_a, %146 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %148 = firrtl.node %147 : !firrtl.uint<1>
  %149 = firrtl.or %res_16_g, %148 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %150 = firrtl.node %149 : !firrtl.uint<1>
  %151 = firrtl.and %res_17_a, %150 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %152 = firrtl.node %151 : !firrtl.uint<1>
  %153 = firrtl.or %res_17_g, %152 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %154 = firrtl.node %153 : !firrtl.uint<1>
  %155 = firrtl.and %res_18_a, %154 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %156 = firrtl.node %155 : !firrtl.uint<1>
  %157 = firrtl.or %res_18_g, %156 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %158 = firrtl.node %157 : !firrtl.uint<1>
  %159 = firrtl.and %res_19_a, %158 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %160 = firrtl.node %159 : !firrtl.uint<1>
  %161 = firrtl.or %res_19_g, %160 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %162 = firrtl.node %161 : !firrtl.uint<1>
  %163 = firrtl.and %res_20_a, %162 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %164 = firrtl.node %163 : !firrtl.uint<1>
  %165 = firrtl.or %res_20_g, %164 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %166 = firrtl.node %165 : !firrtl.uint<1>
  %167 = firrtl.and %res_21_a, %166 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %168 = firrtl.node %167 : !firrtl.uint<1>
  %169 = firrtl.or %res_21_g, %168 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %170 = firrtl.node %169 : !firrtl.uint<1>
  %171 = firrtl.and %res_22_a, %170 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %172 = firrtl.node %171 : !firrtl.uint<1>
  %173 = firrtl.or %res_22_g, %172 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %174 = firrtl.node %173 : !firrtl.uint<1>
  %175 = firrtl.and %res_23_a, %174 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %176 = firrtl.node %175 : !firrtl.uint<1>
  %177 = firrtl.or %res_23_g, %176 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %178 = firrtl.node %177 : !firrtl.uint<1>
  %179 = firrtl.and %res_24_a, %178 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %180 = firrtl.node %179 : !firrtl.uint<1>
  %181 = firrtl.or %res_24_g, %180 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %182 = firrtl.node %181 : !firrtl.uint<1>
  %183 = firrtl.and %res_25_a, %182 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %184 = firrtl.node %183 : !firrtl.uint<1>
  %185 = firrtl.or %res_25_g, %184 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %186 = firrtl.node %185 : !firrtl.uint<1>
  %187 = firrtl.and %res_26_a, %186 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %188 = firrtl.node %187 : !firrtl.uint<1>
  %189 = firrtl.or %res_26_g, %188 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %190 = firrtl.node %189 : !firrtl.uint<1>
  %191 = firrtl.and %res_27_a, %190 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %192 = firrtl.node %191 : !firrtl.uint<1>
  %193 = firrtl.or %res_27_g, %192 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %194 = firrtl.node %193 : !firrtl.uint<1>
  %195 = firrtl.and %res_28_a, %194 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %196 = firrtl.node %195 : !firrtl.uint<1>
  %197 = firrtl.or %res_28_g, %196 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %198 = firrtl.node %197 : !firrtl.uint<1>
  %199 = firrtl.and %res_29_a, %198 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %200 = firrtl.node %199 : !firrtl.uint<1>
  %201 = firrtl.or %res_29_g, %200 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %202 = firrtl.node %201 : !firrtl.uint<1>
  %203 = firrtl.and %res_30_a, %202 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %204 = firrtl.node %203 : !firrtl.uint<1>
  %205 = firrtl.or %res_30_g, %204 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %206 = firrtl.node %205 : !firrtl.uint<1>
  %207 = firrtl.and %res_31_a, %206 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %208 = firrtl.node %207 : !firrtl.uint<1>
  %209 = firrtl.or %res_31_g, %208 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %210 = firrtl.node %209 : !firrtl.uint<1>
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
  firrtl.strictconnect %_cs_WIRE_2, %90 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_3, %94 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_4, %98 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_5, %102 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_6, %106 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_7, %110 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_8, %114 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_9, %118 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_10, %122 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_11, %126 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_12, %130 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_13, %134 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_14, %138 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_15, %142 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_16, %146 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_17, %150 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_18, %154 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_19, %158 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_20, %162 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_21, %166 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_22, %170 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_23, %174 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_24, %178 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_25, %182 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_26, %186 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_27, %190 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_28, %194 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_29, %198 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_30, %202 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_31, %206 : !firrtl.uint<1>
  firrtl.strictconnect %_cs_WIRE_32, %210 : !firrtl.uint<1>
  %211 = firrtl.cat %_cs_WIRE_1, %_cs_WIRE_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_lo_lo_lo_lo = firrtl.node %211 : !firrtl.uint<2>
  %212 = firrtl.cat %_cs_WIRE_3, %_cs_WIRE_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_lo_lo_lo_hi = firrtl.node %212 : !firrtl.uint<2>
  %213 = firrtl.cat %cs_lo_lo_lo_hi, %cs_lo_lo_lo_lo : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<4>
  %cs_lo_lo_lo = firrtl.node %213 : !firrtl.uint<4>
  %214 = firrtl.cat %_cs_WIRE_5, %_cs_WIRE_4 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_lo_lo_hi_lo = firrtl.node %214 : !firrtl.uint<2>
  %215 = firrtl.cat %_cs_WIRE_7, %_cs_WIRE_6 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_lo_lo_hi_hi = firrtl.node %215 : !firrtl.uint<2>
  %216 = firrtl.cat %cs_lo_lo_hi_hi, %cs_lo_lo_hi_lo : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<4>
  %cs_lo_lo_hi = firrtl.node %216 : !firrtl.uint<4>
  %217 = firrtl.cat %cs_lo_lo_hi, %cs_lo_lo_lo : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>
  %cs_lo_lo = firrtl.node %217 : !firrtl.uint<8>
  %218 = firrtl.cat %_cs_WIRE_9, %_cs_WIRE_8 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_lo_hi_lo_lo = firrtl.node %218 : !firrtl.uint<2>
  %219 = firrtl.cat %_cs_WIRE_11, %_cs_WIRE_10 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_lo_hi_lo_hi = firrtl.node %219 : !firrtl.uint<2>
  %220 = firrtl.cat %cs_lo_hi_lo_hi, %cs_lo_hi_lo_lo : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<4>
  %cs_lo_hi_lo = firrtl.node %220 : !firrtl.uint<4>
  %221 = firrtl.cat %_cs_WIRE_13, %_cs_WIRE_12 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_lo_hi_hi_lo = firrtl.node %221 : !firrtl.uint<2>
  %222 = firrtl.cat %_cs_WIRE_15, %_cs_WIRE_14 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_lo_hi_hi_hi = firrtl.node %222 : !firrtl.uint<2>
  %223 = firrtl.cat %cs_lo_hi_hi_hi, %cs_lo_hi_hi_lo : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<4>
  %cs_lo_hi_hi = firrtl.node %223 : !firrtl.uint<4>
  %224 = firrtl.cat %cs_lo_hi_hi, %cs_lo_hi_lo : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>
  %cs_lo_hi = firrtl.node %224 : !firrtl.uint<8>
  %225 = firrtl.cat %cs_lo_hi, %cs_lo_lo : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<16>
  %cs_lo = firrtl.node %225 : !firrtl.uint<16>
  %226 = firrtl.cat %_cs_WIRE_17, %_cs_WIRE_16 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_hi_lo_lo_lo = firrtl.node %226 : !firrtl.uint<2>
  %227 = firrtl.cat %_cs_WIRE_19, %_cs_WIRE_18 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_hi_lo_lo_hi = firrtl.node %227 : !firrtl.uint<2>
  %228 = firrtl.cat %cs_hi_lo_lo_hi, %cs_hi_lo_lo_lo : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<4>
  %cs_hi_lo_lo = firrtl.node %228 : !firrtl.uint<4>
  %229 = firrtl.cat %_cs_WIRE_21, %_cs_WIRE_20 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_hi_lo_hi_lo = firrtl.node %229 : !firrtl.uint<2>
  %230 = firrtl.cat %_cs_WIRE_23, %_cs_WIRE_22 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_hi_lo_hi_hi = firrtl.node %230 : !firrtl.uint<2>
  %231 = firrtl.cat %cs_hi_lo_hi_hi, %cs_hi_lo_hi_lo : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<4>
  %cs_hi_lo_hi = firrtl.node %231 : !firrtl.uint<4>
  %232 = firrtl.cat %cs_hi_lo_hi, %cs_hi_lo_lo : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>
  %cs_hi_lo = firrtl.node %232 : !firrtl.uint<8>
  %233 = firrtl.cat %_cs_WIRE_25, %_cs_WIRE_24 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_hi_hi_lo_lo = firrtl.node %233 : !firrtl.uint<2>
  %234 = firrtl.cat %_cs_WIRE_27, %_cs_WIRE_26 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_hi_hi_lo_hi = firrtl.node %234 : !firrtl.uint<2>
  %235 = firrtl.cat %cs_hi_hi_lo_hi, %cs_hi_hi_lo_lo : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<4>
  %cs_hi_hi_lo = firrtl.node %235 : !firrtl.uint<4>
  %236 = firrtl.cat %_cs_WIRE_29, %_cs_WIRE_28 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_hi_hi_hi_lo = firrtl.node %236 : !firrtl.uint<2>
  %237 = firrtl.cat %_cs_WIRE_32, %_cs_WIRE_31 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %cs_hi_hi_hi_hi_hi = firrtl.node %237 : !firrtl.uint<2>
  %238 = firrtl.cat %cs_hi_hi_hi_hi_hi, %_cs_WIRE_30 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<3>
  %cs_hi_hi_hi_hi = firrtl.node %238 : !firrtl.uint<3>
  %239 = firrtl.cat %cs_hi_hi_hi_hi, %cs_hi_hi_hi_lo : (!firrtl.uint<3>, !firrtl.uint<2>) -> !firrtl.uint<5>
  %cs_hi_hi_hi = firrtl.node %239 : !firrtl.uint<5>
  %240 = firrtl.cat %cs_hi_hi_hi, %cs_hi_hi_lo : (!firrtl.uint<5>, !firrtl.uint<4>) -> !firrtl.uint<9>
  %cs_hi_hi = firrtl.node %240 : !firrtl.uint<9>
  %241 = firrtl.cat %cs_hi_hi, %cs_hi_lo : (!firrtl.uint<9>, !firrtl.uint<8>) -> !firrtl.uint<17>
  %cs_hi = firrtl.node %241 : !firrtl.uint<17>
  %242 = firrtl.cat %cs_hi, %cs_lo : (!firrtl.uint<17>, !firrtl.uint<16>) -> !firrtl.uint<33>
  %cs = firrtl.node %242 : !firrtl.uint<33>
  %243 = firrtl.bits %cs 31 to 0 : (!firrtl.uint<33>) -> !firrtl.uint<32>
  %_io_c_T = firrtl.node %243 : !firrtl.uint<32>
  %244 = firrtl.xor %p, %_io_c_T : (!firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %_io_c_T_1 = firrtl.node %244 : !firrtl.uint<32>
  firrtl.strictconnect %io_c_3, %_io_c_T_1 : !firrtl.uint<32>
  %245 = firrtl.bits %cs 32 to 32 : (!firrtl.uint<33>) -> !firrtl.uint<1>
  %_io_cout_T = firrtl.node %245 : !firrtl.uint<1>
  firrtl.strictconnect %io_cout_4, %_io_cout_T : !firrtl.uint<1>
}

