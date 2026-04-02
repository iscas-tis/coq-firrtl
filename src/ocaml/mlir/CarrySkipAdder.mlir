// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @CarrySkipAdder(in %clock1: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_a: !firrtl.uint<32>, in %io_b: !firrtl.uint<32>, in %io_cin: !firrtl.uint<1>, out %io_c: !firrtl.uint<32>, out %io_cout: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
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
  %res_0 = firrtl.wire : !firrtl.uint<4>
  %res_1 = firrtl.wire : !firrtl.uint<4>
  %res_2 = firrtl.wire : !firrtl.uint<4>
  %res_3 = firrtl.wire : !firrtl.uint<4>
  %res_4 = firrtl.wire : !firrtl.uint<4>
  %res_5 = firrtl.wire : !firrtl.uint<4>
  %res_6 = firrtl.wire : !firrtl.uint<4>
  %res_7 = firrtl.wire : !firrtl.uint<4>
  %couts_0 = firrtl.wire : !firrtl.uint<1>
  %couts_1 = firrtl.wire : !firrtl.uint<1>
  %couts_2 = firrtl.wire : !firrtl.uint<1>
  %couts_3 = firrtl.wire : !firrtl.uint<1>
  %couts_4 = firrtl.wire : !firrtl.uint<1>
  %couts_5 = firrtl.wire : !firrtl.uint<1>
  %couts_6 = firrtl.wire : !firrtl.uint<1>
  %couts_7 = firrtl.wire : !firrtl.uint<1>
  %couts_8 = firrtl.wire : !firrtl.uint<1>
  firrtl.strictconnect %couts_0, %io_cin_2 : !firrtl.uint<1>
  %16 = firrtl.add %aOp_0, %bOp_0 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<5>
  %_sum_T = firrtl.node %16 : !firrtl.uint<5>
  %17 = firrtl.add %_sum_T, %couts_0 : (!firrtl.uint<5>, !firrtl.uint<1>) -> !firrtl.uint<6>
  %_sum_T_1 = firrtl.node %17 : !firrtl.uint<6>
  %18 = firrtl.tail %_sum_T_1, 1 : (!firrtl.uint<6>) -> !firrtl.uint<5>
  %sum = firrtl.node %18 : !firrtl.uint<5>
  %19 = firrtl.bits %sum 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_0_T = firrtl.node %19 : !firrtl.uint<4>
  firrtl.strictconnect %res_0, %_res_0_T : !firrtl.uint<4>
  %20 = firrtl.xor %aOp_0, %bOp_0 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_couts_1_T = firrtl.node %20 : !firrtl.uint<4>
  %21 = firrtl.andr %_couts_1_T : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_couts_1_T_1 = firrtl.node %21 : !firrtl.uint<1>
  %22 = firrtl.bits %sum 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_1_T_2 = firrtl.node %22 : !firrtl.uint<1>
  %23 = firrtl.mux(%_couts_1_T_1, %couts_0, %_couts_1_T_2) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_couts_1_T_3 = firrtl.node %23 : !firrtl.uint<1>
  firrtl.strictconnect %couts_1, %_couts_1_T_3 : !firrtl.uint<1>
  %24 = firrtl.add %aOp_1, %bOp_1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<5>
  %_sum_T_2 = firrtl.node %24 : !firrtl.uint<5>
  %25 = firrtl.add %_sum_T_2, %couts_1 : (!firrtl.uint<5>, !firrtl.uint<1>) -> !firrtl.uint<6>
  %_sum_T_3 = firrtl.node %25 : !firrtl.uint<6>
  %26 = firrtl.tail %_sum_T_3, 1 : (!firrtl.uint<6>) -> !firrtl.uint<5>
  %sum_1 = firrtl.node %26 : !firrtl.uint<5>
  %27 = firrtl.bits %sum_1 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_1_T = firrtl.node %27 : !firrtl.uint<4>
  firrtl.strictconnect %res_1, %_res_1_T : !firrtl.uint<4>
  %28 = firrtl.xor %aOp_1, %bOp_1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_couts_2_T = firrtl.node %28 : !firrtl.uint<4>
  %29 = firrtl.andr %_couts_2_T : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_couts_2_T_1 = firrtl.node %29 : !firrtl.uint<1>
  %30 = firrtl.bits %sum_1 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_2_T_2 = firrtl.node %30 : !firrtl.uint<1>
  %31 = firrtl.mux(%_couts_2_T_1, %couts_1, %_couts_2_T_2) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_couts_2_T_3 = firrtl.node %31 : !firrtl.uint<1>
  firrtl.strictconnect %couts_2, %_couts_2_T_3 : !firrtl.uint<1>
  %32 = firrtl.add %aOp_2, %bOp_2 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<5>
  %_sum_T_4 = firrtl.node %32 : !firrtl.uint<5>
  %33 = firrtl.add %_sum_T_4, %couts_2 : (!firrtl.uint<5>, !firrtl.uint<1>) -> !firrtl.uint<6>
  %_sum_T_5 = firrtl.node %33 : !firrtl.uint<6>
  %34 = firrtl.tail %_sum_T_5, 1 : (!firrtl.uint<6>) -> !firrtl.uint<5>
  %sum_2 = firrtl.node %34 : !firrtl.uint<5>
  %35 = firrtl.bits %sum_2 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_2_T = firrtl.node %35 : !firrtl.uint<4>
  firrtl.strictconnect %res_2, %_res_2_T : !firrtl.uint<4>
  %36 = firrtl.xor %aOp_2, %bOp_2 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_couts_3_T = firrtl.node %36 : !firrtl.uint<4>
  %37 = firrtl.andr %_couts_3_T : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_couts_3_T_1 = firrtl.node %37 : !firrtl.uint<1>
  %38 = firrtl.bits %sum_2 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_3_T_2 = firrtl.node %38 : !firrtl.uint<1>
  %39 = firrtl.mux(%_couts_3_T_1, %couts_2, %_couts_3_T_2) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_couts_3_T_3 = firrtl.node %39 : !firrtl.uint<1>
  firrtl.strictconnect %couts_3, %_couts_3_T_3 : !firrtl.uint<1>
  %40 = firrtl.add %aOp_3, %bOp_3 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<5>
  %_sum_T_6 = firrtl.node %40 : !firrtl.uint<5>
  %41 = firrtl.add %_sum_T_6, %couts_3 : (!firrtl.uint<5>, !firrtl.uint<1>) -> !firrtl.uint<6>
  %_sum_T_7 = firrtl.node %41 : !firrtl.uint<6>
  %42 = firrtl.tail %_sum_T_7, 1 : (!firrtl.uint<6>) -> !firrtl.uint<5>
  %sum_3 = firrtl.node %42 : !firrtl.uint<5>
  %43 = firrtl.bits %sum_3 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_3_T = firrtl.node %43 : !firrtl.uint<4>
  firrtl.strictconnect %res_3, %_res_3_T : !firrtl.uint<4>
  %44 = firrtl.xor %aOp_3, %bOp_3 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_couts_4_T = firrtl.node %44 : !firrtl.uint<4>
  %45 = firrtl.andr %_couts_4_T : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_couts_4_T_1 = firrtl.node %45 : !firrtl.uint<1>
  %46 = firrtl.bits %sum_3 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_4_T_2 = firrtl.node %46 : !firrtl.uint<1>
  %47 = firrtl.mux(%_couts_4_T_1, %couts_3, %_couts_4_T_2) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_couts_4_T_3 = firrtl.node %47 : !firrtl.uint<1>
  firrtl.strictconnect %couts_4, %_couts_4_T_3 : !firrtl.uint<1>
  %48 = firrtl.add %aOp_4, %bOp_4 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<5>
  %_sum_T_8 = firrtl.node %48 : !firrtl.uint<5>
  %49 = firrtl.add %_sum_T_8, %couts_4 : (!firrtl.uint<5>, !firrtl.uint<1>) -> !firrtl.uint<6>
  %_sum_T_9 = firrtl.node %49 : !firrtl.uint<6>
  %50 = firrtl.tail %_sum_T_9, 1 : (!firrtl.uint<6>) -> !firrtl.uint<5>
  %sum_4 = firrtl.node %50 : !firrtl.uint<5>
  %51 = firrtl.bits %sum_4 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_4_T = firrtl.node %51 : !firrtl.uint<4>
  firrtl.strictconnect %res_4, %_res_4_T : !firrtl.uint<4>
  %52 = firrtl.xor %aOp_4, %bOp_4 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_couts_5_T = firrtl.node %52 : !firrtl.uint<4>
  %53 = firrtl.andr %_couts_5_T : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_couts_5_T_1 = firrtl.node %53 : !firrtl.uint<1>
  %54 = firrtl.bits %sum_4 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_5_T_2 = firrtl.node %54 : !firrtl.uint<1>
  %55 = firrtl.mux(%_couts_5_T_1, %couts_4, %_couts_5_T_2) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_couts_5_T_3 = firrtl.node %55 : !firrtl.uint<1>
  firrtl.strictconnect %couts_5, %_couts_5_T_3 : !firrtl.uint<1>
  %56 = firrtl.add %aOp_5, %bOp_5 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<5>
  %_sum_T_10 = firrtl.node %56 : !firrtl.uint<5>
  %57 = firrtl.add %_sum_T_10, %couts_5 : (!firrtl.uint<5>, !firrtl.uint<1>) -> !firrtl.uint<6>
  %_sum_T_11 = firrtl.node %57 : !firrtl.uint<6>
  %58 = firrtl.tail %_sum_T_11, 1 : (!firrtl.uint<6>) -> !firrtl.uint<5>
  %sum_5 = firrtl.node %58 : !firrtl.uint<5>
  %59 = firrtl.bits %sum_5 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_5_T = firrtl.node %59 : !firrtl.uint<4>
  firrtl.strictconnect %res_5, %_res_5_T : !firrtl.uint<4>
  %60 = firrtl.xor %aOp_5, %bOp_5 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_couts_6_T = firrtl.node %60 : !firrtl.uint<4>
  %61 = firrtl.andr %_couts_6_T : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_couts_6_T_1 = firrtl.node %61 : !firrtl.uint<1>
  %62 = firrtl.bits %sum_5 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_6_T_2 = firrtl.node %62 : !firrtl.uint<1>
  %63 = firrtl.mux(%_couts_6_T_1, %couts_5, %_couts_6_T_2) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_couts_6_T_3 = firrtl.node %63 : !firrtl.uint<1>
  firrtl.strictconnect %couts_6, %_couts_6_T_3 : !firrtl.uint<1>
  %64 = firrtl.add %aOp_6, %bOp_6 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<5>
  %_sum_T_12 = firrtl.node %64 : !firrtl.uint<5>
  %65 = firrtl.add %_sum_T_12, %couts_6 : (!firrtl.uint<5>, !firrtl.uint<1>) -> !firrtl.uint<6>
  %_sum_T_13 = firrtl.node %65 : !firrtl.uint<6>
  %66 = firrtl.tail %_sum_T_13, 1 : (!firrtl.uint<6>) -> !firrtl.uint<5>
  %sum_6 = firrtl.node %66 : !firrtl.uint<5>
  %67 = firrtl.bits %sum_6 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_6_T = firrtl.node %67 : !firrtl.uint<4>
  firrtl.strictconnect %res_6, %_res_6_T : !firrtl.uint<4>
  %68 = firrtl.xor %aOp_6, %bOp_6 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_couts_7_T = firrtl.node %68 : !firrtl.uint<4>
  %69 = firrtl.andr %_couts_7_T : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_couts_7_T_1 = firrtl.node %69 : !firrtl.uint<1>
  %70 = firrtl.bits %sum_6 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_7_T_2 = firrtl.node %70 : !firrtl.uint<1>
  %71 = firrtl.mux(%_couts_7_T_1, %couts_6, %_couts_7_T_2) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_couts_7_T_3 = firrtl.node %71 : !firrtl.uint<1>
  firrtl.strictconnect %couts_7, %_couts_7_T_3 : !firrtl.uint<1>
  %72 = firrtl.add %aOp_7, %bOp_7 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<5>
  %_sum_T_14 = firrtl.node %72 : !firrtl.uint<5>
  %73 = firrtl.add %_sum_T_14, %couts_7 : (!firrtl.uint<5>, !firrtl.uint<1>) -> !firrtl.uint<6>
  %_sum_T_15 = firrtl.node %73 : !firrtl.uint<6>
  %74 = firrtl.tail %_sum_T_15, 1 : (!firrtl.uint<6>) -> !firrtl.uint<5>
  %sum_7 = firrtl.node %74 : !firrtl.uint<5>
  %75 = firrtl.bits %sum_7 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_7_T = firrtl.node %75 : !firrtl.uint<4>
  firrtl.strictconnect %res_7, %_res_7_T : !firrtl.uint<4>
  %76 = firrtl.xor %aOp_7, %bOp_7 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_couts_8_T = firrtl.node %76 : !firrtl.uint<4>
  %77 = firrtl.andr %_couts_8_T : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_couts_8_T_1 = firrtl.node %77 : !firrtl.uint<1>
  %78 = firrtl.bits %sum_7 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_8_T_2 = firrtl.node %78 : !firrtl.uint<1>
  %79 = firrtl.mux(%_couts_8_T_1, %couts_7, %_couts_8_T_2) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_couts_8_T_3 = firrtl.node %79 : !firrtl.uint<1>
  firrtl.strictconnect %couts_8, %_couts_8_T_3 : !firrtl.uint<1>
  %80 = firrtl.cat %res_1, %res_0 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>
  %io_c_lo_lo = firrtl.node %80 : !firrtl.uint<8>
  %81 = firrtl.cat %res_3, %res_2 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>
  %io_c_lo_hi = firrtl.node %81 : !firrtl.uint<8>
  %82 = firrtl.cat %io_c_lo_hi, %io_c_lo_lo : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<16>
  %io_c_lo = firrtl.node %82 : !firrtl.uint<16>
  %83 = firrtl.cat %res_5, %res_4 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>
  %io_c_hi_lo = firrtl.node %83 : !firrtl.uint<8>
  %84 = firrtl.cat %res_7, %res_6 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>
  %io_c_hi_hi = firrtl.node %84 : !firrtl.uint<8>
  %85 = firrtl.cat %io_c_hi_hi, %io_c_hi_lo : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<16>
  %io_c_hi = firrtl.node %85 : !firrtl.uint<16>
  %86 = firrtl.cat %io_c_hi, %io_c_lo : (!firrtl.uint<16>, !firrtl.uint<16>) -> !firrtl.uint<32>
  %_io_c_T = firrtl.node %86 : !firrtl.uint<32>
  %87 = firrtl.bits %_io_c_T 31 to 0 : (!firrtl.uint<32>) -> !firrtl.uint<32>
  %_io_c_T_1 = firrtl.node %87 : !firrtl.uint<32>
  firrtl.strictconnect %io_c_3, %_io_c_T_1 : !firrtl.uint<32>
  firrtl.strictconnect %io_cout_4, %couts_8 : !firrtl.uint<1>
}

