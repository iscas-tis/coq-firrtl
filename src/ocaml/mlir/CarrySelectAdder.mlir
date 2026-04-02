// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @CarrySelectAdder(in %clock1: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_a: !firrtl.uint<32>, in %io_b: !firrtl.uint<32>, in %io_cin: !firrtl.uint<1>, out %io_c: !firrtl.uint<32>, out %io_cout: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
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
  %c0Sum = firrtl.node %16 : !firrtl.uint<5>
  %17 = firrtl.node %16 : !firrtl.uint<5>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %18 = firrtl.add %17, %c1_ui1 : (!firrtl.uint<5>, !firrtl.uint<1>) -> !firrtl.uint<6>
  %19 = firrtl.node %18 : !firrtl.uint<6>
  %20 = firrtl.tail %19, 1 : (!firrtl.uint<6>) -> !firrtl.uint<5>
  %c1Sum = firrtl.node %20 : !firrtl.uint<5>
  %21 = firrtl.bits %c1Sum 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_0_T = firrtl.node %21 : !firrtl.uint<4>
  %22 = firrtl.bits %c0Sum 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_0_T_1 = firrtl.node %22 : !firrtl.uint<4>
  %23 = firrtl.mux(%couts_0, %_res_0_T, %_res_0_T_1) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_res_0_T_2 = firrtl.node %23 : !firrtl.uint<4>
  firrtl.strictconnect %res_0, %_res_0_T_2 : !firrtl.uint<4>
  %24 = firrtl.bits %c1Sum 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_1_T = firrtl.node %24 : !firrtl.uint<1>
  %25 = firrtl.bits %c0Sum 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_1_T_1 = firrtl.node %25 : !firrtl.uint<1>
  %26 = firrtl.mux(%couts_0, %_couts_1_T, %_couts_1_T_1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_couts_1_T_2 = firrtl.node %26 : !firrtl.uint<1>
  firrtl.strictconnect %couts_1, %_couts_1_T_2 : !firrtl.uint<1>
  %27 = firrtl.add %aOp_1, %bOp_1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<5>
  %c0Sum_1 = firrtl.node %27 : !firrtl.uint<5>
  %28 = firrtl.node %27 : !firrtl.uint<5>
  %29 = firrtl.add %28, %c1_ui1 : (!firrtl.uint<5>, !firrtl.uint<1>) -> !firrtl.uint<6>
  %30 = firrtl.node %29 : !firrtl.uint<6>
  %31 = firrtl.tail %30, 1 : (!firrtl.uint<6>) -> !firrtl.uint<5>
  %c1Sum_1 = firrtl.node %31 : !firrtl.uint<5>
  %32 = firrtl.bits %c1Sum_1 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_1_T = firrtl.node %32 : !firrtl.uint<4>
  %33 = firrtl.bits %c0Sum_1 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_1_T_1 = firrtl.node %33 : !firrtl.uint<4>
  %34 = firrtl.mux(%couts_1, %_res_1_T, %_res_1_T_1) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_res_1_T_2 = firrtl.node %34 : !firrtl.uint<4>
  firrtl.strictconnect %res_1, %_res_1_T_2 : !firrtl.uint<4>
  %35 = firrtl.bits %c1Sum_1 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_2_T = firrtl.node %35 : !firrtl.uint<1>
  %36 = firrtl.bits %c0Sum_1 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_2_T_1 = firrtl.node %36 : !firrtl.uint<1>
  %37 = firrtl.mux(%couts_1, %_couts_2_T, %_couts_2_T_1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_couts_2_T_2 = firrtl.node %37 : !firrtl.uint<1>
  firrtl.strictconnect %couts_2, %_couts_2_T_2 : !firrtl.uint<1>
  %38 = firrtl.add %aOp_2, %bOp_2 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<5>
  %c0Sum_2 = firrtl.node %38 : !firrtl.uint<5>
  %39 = firrtl.node %38 : !firrtl.uint<5>
  %40 = firrtl.add %39, %c1_ui1 : (!firrtl.uint<5>, !firrtl.uint<1>) -> !firrtl.uint<6>
  %41 = firrtl.node %40 : !firrtl.uint<6>
  %42 = firrtl.tail %41, 1 : (!firrtl.uint<6>) -> !firrtl.uint<5>
  %c1Sum_2 = firrtl.node %42 : !firrtl.uint<5>
  %43 = firrtl.bits %c1Sum_2 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_2_T = firrtl.node %43 : !firrtl.uint<4>
  %44 = firrtl.bits %c0Sum_2 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_2_T_1 = firrtl.node %44 : !firrtl.uint<4>
  %45 = firrtl.mux(%couts_2, %_res_2_T, %_res_2_T_1) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_res_2_T_2 = firrtl.node %45 : !firrtl.uint<4>
  firrtl.strictconnect %res_2, %_res_2_T_2 : !firrtl.uint<4>
  %46 = firrtl.bits %c1Sum_2 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_3_T = firrtl.node %46 : !firrtl.uint<1>
  %47 = firrtl.bits %c0Sum_2 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_3_T_1 = firrtl.node %47 : !firrtl.uint<1>
  %48 = firrtl.mux(%couts_2, %_couts_3_T, %_couts_3_T_1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_couts_3_T_2 = firrtl.node %48 : !firrtl.uint<1>
  firrtl.strictconnect %couts_3, %_couts_3_T_2 : !firrtl.uint<1>
  %49 = firrtl.add %aOp_3, %bOp_3 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<5>
  %c0Sum_3 = firrtl.node %49 : !firrtl.uint<5>
  %50 = firrtl.node %49 : !firrtl.uint<5>
  %51 = firrtl.add %50, %c1_ui1 : (!firrtl.uint<5>, !firrtl.uint<1>) -> !firrtl.uint<6>
  %52 = firrtl.node %51 : !firrtl.uint<6>
  %53 = firrtl.tail %52, 1 : (!firrtl.uint<6>) -> !firrtl.uint<5>
  %c1Sum_3 = firrtl.node %53 : !firrtl.uint<5>
  %54 = firrtl.bits %c1Sum_3 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_3_T = firrtl.node %54 : !firrtl.uint<4>
  %55 = firrtl.bits %c0Sum_3 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_3_T_1 = firrtl.node %55 : !firrtl.uint<4>
  %56 = firrtl.mux(%couts_3, %_res_3_T, %_res_3_T_1) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_res_3_T_2 = firrtl.node %56 : !firrtl.uint<4>
  firrtl.strictconnect %res_3, %_res_3_T_2 : !firrtl.uint<4>
  %57 = firrtl.bits %c1Sum_3 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_4_T = firrtl.node %57 : !firrtl.uint<1>
  %58 = firrtl.bits %c0Sum_3 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_4_T_1 = firrtl.node %58 : !firrtl.uint<1>
  %59 = firrtl.mux(%couts_3, %_couts_4_T, %_couts_4_T_1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_couts_4_T_2 = firrtl.node %59 : !firrtl.uint<1>
  firrtl.strictconnect %couts_4, %_couts_4_T_2 : !firrtl.uint<1>
  %60 = firrtl.add %aOp_4, %bOp_4 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<5>
  %c0Sum_4 = firrtl.node %60 : !firrtl.uint<5>
  %61 = firrtl.node %60 : !firrtl.uint<5>
  %62 = firrtl.add %61, %c1_ui1 : (!firrtl.uint<5>, !firrtl.uint<1>) -> !firrtl.uint<6>
  %63 = firrtl.node %62 : !firrtl.uint<6>
  %64 = firrtl.tail %63, 1 : (!firrtl.uint<6>) -> !firrtl.uint<5>
  %c1Sum_4 = firrtl.node %64 : !firrtl.uint<5>
  %65 = firrtl.bits %c1Sum_4 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_4_T = firrtl.node %65 : !firrtl.uint<4>
  %66 = firrtl.bits %c0Sum_4 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_4_T_1 = firrtl.node %66 : !firrtl.uint<4>
  %67 = firrtl.mux(%couts_4, %_res_4_T, %_res_4_T_1) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_res_4_T_2 = firrtl.node %67 : !firrtl.uint<4>
  firrtl.strictconnect %res_4, %_res_4_T_2 : !firrtl.uint<4>
  %68 = firrtl.bits %c1Sum_4 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_5_T = firrtl.node %68 : !firrtl.uint<1>
  %69 = firrtl.bits %c0Sum_4 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_5_T_1 = firrtl.node %69 : !firrtl.uint<1>
  %70 = firrtl.mux(%couts_4, %_couts_5_T, %_couts_5_T_1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_couts_5_T_2 = firrtl.node %70 : !firrtl.uint<1>
  firrtl.strictconnect %couts_5, %_couts_5_T_2 : !firrtl.uint<1>
  %71 = firrtl.add %aOp_5, %bOp_5 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<5>
  %c0Sum_5 = firrtl.node %71 : !firrtl.uint<5>
  %72 = firrtl.node %71 : !firrtl.uint<5>
  %73 = firrtl.add %72, %c1_ui1 : (!firrtl.uint<5>, !firrtl.uint<1>) -> !firrtl.uint<6>
  %74 = firrtl.node %73 : !firrtl.uint<6>
  %75 = firrtl.tail %74, 1 : (!firrtl.uint<6>) -> !firrtl.uint<5>
  %c1Sum_5 = firrtl.node %75 : !firrtl.uint<5>
  %76 = firrtl.bits %c1Sum_5 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_5_T = firrtl.node %76 : !firrtl.uint<4>
  %77 = firrtl.bits %c0Sum_5 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_5_T_1 = firrtl.node %77 : !firrtl.uint<4>
  %78 = firrtl.mux(%couts_5, %_res_5_T, %_res_5_T_1) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_res_5_T_2 = firrtl.node %78 : !firrtl.uint<4>
  firrtl.strictconnect %res_5, %_res_5_T_2 : !firrtl.uint<4>
  %79 = firrtl.bits %c1Sum_5 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_6_T = firrtl.node %79 : !firrtl.uint<1>
  %80 = firrtl.bits %c0Sum_5 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_6_T_1 = firrtl.node %80 : !firrtl.uint<1>
  %81 = firrtl.mux(%couts_5, %_couts_6_T, %_couts_6_T_1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_couts_6_T_2 = firrtl.node %81 : !firrtl.uint<1>
  firrtl.strictconnect %couts_6, %_couts_6_T_2 : !firrtl.uint<1>
  %82 = firrtl.add %aOp_6, %bOp_6 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<5>
  %c0Sum_6 = firrtl.node %82 : !firrtl.uint<5>
  %83 = firrtl.node %82 : !firrtl.uint<5>
  %84 = firrtl.add %83, %c1_ui1 : (!firrtl.uint<5>, !firrtl.uint<1>) -> !firrtl.uint<6>
  %85 = firrtl.node %84 : !firrtl.uint<6>
  %86 = firrtl.tail %85, 1 : (!firrtl.uint<6>) -> !firrtl.uint<5>
  %c1Sum_6 = firrtl.node %86 : !firrtl.uint<5>
  %87 = firrtl.bits %c1Sum_6 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_6_T = firrtl.node %87 : !firrtl.uint<4>
  %88 = firrtl.bits %c0Sum_6 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_6_T_1 = firrtl.node %88 : !firrtl.uint<4>
  %89 = firrtl.mux(%couts_6, %_res_6_T, %_res_6_T_1) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_res_6_T_2 = firrtl.node %89 : !firrtl.uint<4>
  firrtl.strictconnect %res_6, %_res_6_T_2 : !firrtl.uint<4>
  %90 = firrtl.bits %c1Sum_6 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_7_T = firrtl.node %90 : !firrtl.uint<1>
  %91 = firrtl.bits %c0Sum_6 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_7_T_1 = firrtl.node %91 : !firrtl.uint<1>
  %92 = firrtl.mux(%couts_6, %_couts_7_T, %_couts_7_T_1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_couts_7_T_2 = firrtl.node %92 : !firrtl.uint<1>
  firrtl.strictconnect %couts_7, %_couts_7_T_2 : !firrtl.uint<1>
  %93 = firrtl.add %aOp_7, %bOp_7 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<5>
  %c0Sum_7 = firrtl.node %93 : !firrtl.uint<5>
  %94 = firrtl.node %93 : !firrtl.uint<5>
  %95 = firrtl.add %94, %c1_ui1 : (!firrtl.uint<5>, !firrtl.uint<1>) -> !firrtl.uint<6>
  %96 = firrtl.node %95 : !firrtl.uint<6>
  %97 = firrtl.tail %96, 1 : (!firrtl.uint<6>) -> !firrtl.uint<5>
  %c1Sum_7 = firrtl.node %97 : !firrtl.uint<5>
  %98 = firrtl.bits %c1Sum_7 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_7_T = firrtl.node %98 : !firrtl.uint<4>
  %99 = firrtl.bits %c0Sum_7 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_7_T_1 = firrtl.node %99 : !firrtl.uint<4>
  %100 = firrtl.mux(%couts_7, %_res_7_T, %_res_7_T_1) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_res_7_T_2 = firrtl.node %100 : !firrtl.uint<4>
  firrtl.strictconnect %res_7, %_res_7_T_2 : !firrtl.uint<4>
  %101 = firrtl.bits %c1Sum_7 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_8_T = firrtl.node %101 : !firrtl.uint<1>
  %102 = firrtl.bits %c0Sum_7 4 to 4 : (!firrtl.uint<5>) -> !firrtl.uint<1>
  %_couts_8_T_1 = firrtl.node %102 : !firrtl.uint<1>
  %103 = firrtl.mux(%couts_7, %_couts_8_T, %_couts_8_T_1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_couts_8_T_2 = firrtl.node %103 : !firrtl.uint<1>
  firrtl.strictconnect %couts_8, %_couts_8_T_2 : !firrtl.uint<1>
  %104 = firrtl.cat %res_1, %res_0 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>
  %io_c_lo_lo = firrtl.node %104 : !firrtl.uint<8>
  %105 = firrtl.cat %res_3, %res_2 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>
  %io_c_lo_hi = firrtl.node %105 : !firrtl.uint<8>
  %106 = firrtl.cat %io_c_lo_hi, %io_c_lo_lo : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<16>
  %io_c_lo = firrtl.node %106 : !firrtl.uint<16>
  %107 = firrtl.cat %res_5, %res_4 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>
  %io_c_hi_lo = firrtl.node %107 : !firrtl.uint<8>
  %108 = firrtl.cat %res_7, %res_6 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>
  %io_c_hi_hi = firrtl.node %108 : !firrtl.uint<8>
  %109 = firrtl.cat %io_c_hi_hi, %io_c_hi_lo : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<16>
  %io_c_hi = firrtl.node %109 : !firrtl.uint<16>
  %110 = firrtl.cat %io_c_hi, %io_c_lo : (!firrtl.uint<16>, !firrtl.uint<16>) -> !firrtl.uint<32>
  %_io_c_T = firrtl.node %110 : !firrtl.uint<32>
  %111 = firrtl.bits %_io_c_T 31 to 0 : (!firrtl.uint<32>) -> !firrtl.uint<32>
  %_io_c_T_1 = firrtl.node %111 : !firrtl.uint<32>
  firrtl.strictconnect %io_c_3, %_io_c_T_1 : !firrtl.uint<32>
  firrtl.strictconnect %io_cout_4, %couts_8 : !firrtl.uint<1>
}

