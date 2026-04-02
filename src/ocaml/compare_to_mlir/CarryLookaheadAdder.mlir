// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @CarryLookaheadAdder(in %clock1: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_a: !firrtl.uint<32>, in %io_b: !firrtl.uint<32>, in %io_cin: !firrtl.uint<1>, out %io_c: !firrtl.uint<32>, out %io_cout: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
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
  %16 = firrtl.xor %aOp_0, %bOp_0 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %p = firrtl.node %16 : !firrtl.uint<4>
  %17 = firrtl.and %aOp_0, %bOp_0 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %g = firrtl.node %17 : !firrtl.uint<4>
  %cs_0 = firrtl.wire : !firrtl.uint<1>
  %cs_1 = firrtl.wire : !firrtl.uint<1>
  %cs_2 = firrtl.wire : !firrtl.uint<1>
  %cs_3 = firrtl.wire : !firrtl.uint<1>
  %cs_4 = firrtl.wire : !firrtl.uint<1>
  firrtl.strictconnect %cs_0, %couts_0 : !firrtl.uint<1>
  %18 = firrtl.bits %g 0 to 0 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_1_T = firrtl.node %18 : !firrtl.uint<1>
  %19 = firrtl.bits %p 0 to 0 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_1_T_1 = firrtl.node %19 : !firrtl.uint<1>
  %20 = firrtl.and %_cs_1_T_1, %cs_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_1_T_2 = firrtl.node %20 : !firrtl.uint<1>
  %21 = firrtl.or %_cs_1_T, %_cs_1_T_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_1_T_3 = firrtl.node %21 : !firrtl.uint<1>
  firrtl.strictconnect %cs_1, %_cs_1_T_3 : !firrtl.uint<1>
  %22 = firrtl.bits %g 1 to 1 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_2_T = firrtl.node %22 : !firrtl.uint<1>
  %23 = firrtl.bits %p 1 to 1 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_2_T_1 = firrtl.node %23 : !firrtl.uint<1>
  %24 = firrtl.and %_cs_2_T_1, %cs_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_2_T_2 = firrtl.node %24 : !firrtl.uint<1>
  %25 = firrtl.or %_cs_2_T, %_cs_2_T_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_2_T_3 = firrtl.node %25 : !firrtl.uint<1>
  firrtl.strictconnect %cs_2, %_cs_2_T_3 : !firrtl.uint<1>
  %26 = firrtl.bits %g 2 to 2 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_3_T = firrtl.node %26 : !firrtl.uint<1>
  %27 = firrtl.bits %p 2 to 2 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_3_T_1 = firrtl.node %27 : !firrtl.uint<1>
  %28 = firrtl.and %_cs_3_T_1, %cs_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_3_T_2 = firrtl.node %28 : !firrtl.uint<1>
  %29 = firrtl.or %_cs_3_T, %_cs_3_T_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_3_T_3 = firrtl.node %29 : !firrtl.uint<1>
  firrtl.strictconnect %cs_3, %_cs_3_T_3 : !firrtl.uint<1>
  %30 = firrtl.bits %g 3 to 3 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_4_T = firrtl.node %30 : !firrtl.uint<1>
  %31 = firrtl.bits %p 3 to 3 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_4_T_1 = firrtl.node %31 : !firrtl.uint<1>
  %32 = firrtl.and %_cs_4_T_1, %cs_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_4_T_2 = firrtl.node %32 : !firrtl.uint<1>
  %33 = firrtl.or %_cs_4_T, %_cs_4_T_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_4_T_3 = firrtl.node %33 : !firrtl.uint<1>
  firrtl.strictconnect %cs_4, %_cs_4_T_3 : !firrtl.uint<1>
  %34 = firrtl.cat %cs_1, %cs_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %res_0_lo = firrtl.node %34 : !firrtl.uint<2>
  %35 = firrtl.cat %cs_4, %cs_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %res_0_hi_hi = firrtl.node %35 : !firrtl.uint<2>
  %36 = firrtl.cat %res_0_hi_hi, %cs_2 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<3>
  %res_0_hi = firrtl.node %36 : !firrtl.uint<3>
  %37 = firrtl.cat %res_0_hi, %res_0_lo : (!firrtl.uint<3>, !firrtl.uint<2>) -> !firrtl.uint<5>
  %_res_0_T = firrtl.node %37 : !firrtl.uint<5>
  %38 = firrtl.bits %_res_0_T 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_0_T_1 = firrtl.node %38 : !firrtl.uint<4>
  %39 = firrtl.xor %p, %_res_0_T_1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_res_0_T_2 = firrtl.node %39 : !firrtl.uint<4>
  firrtl.strictconnect %res_0, %_res_0_T_2 : !firrtl.uint<4>
  firrtl.strictconnect %couts_1, %cs_4 : !firrtl.uint<1>
  %40 = firrtl.xor %aOp_1, %bOp_1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %p_1 = firrtl.node %40 : !firrtl.uint<4>
  %41 = firrtl.and %aOp_1, %bOp_1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %g_1 = firrtl.node %41 : !firrtl.uint<4>
  %cs_1_0 = firrtl.wire : !firrtl.uint<1>
  %cs_1_1 = firrtl.wire : !firrtl.uint<1>
  %cs_1_2 = firrtl.wire : !firrtl.uint<1>
  %cs_1_3 = firrtl.wire : !firrtl.uint<1>
  %cs_1_4 = firrtl.wire : !firrtl.uint<1>
  firrtl.strictconnect %cs_1_0, %couts_1 : !firrtl.uint<1>
  %42 = firrtl.bits %g_1 0 to 0 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_1_T_4 = firrtl.node %42 : !firrtl.uint<1>
  %43 = firrtl.bits %p_1 0 to 0 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_1_T_5 = firrtl.node %43 : !firrtl.uint<1>
  %44 = firrtl.and %_cs_1_T_5, %cs_1_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_1_T_6 = firrtl.node %44 : !firrtl.uint<1>
  %45 = firrtl.or %_cs_1_T_4, %_cs_1_T_6 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_1_T_7 = firrtl.node %45 : !firrtl.uint<1>
  firrtl.strictconnect %cs_1_1, %_cs_1_T_7 : !firrtl.uint<1>
  %46 = firrtl.bits %g_1 1 to 1 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_2_T_4 = firrtl.node %46 : !firrtl.uint<1>
  %47 = firrtl.bits %p_1 1 to 1 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_2_T_5 = firrtl.node %47 : !firrtl.uint<1>
  %48 = firrtl.and %_cs_2_T_5, %cs_1_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_2_T_6 = firrtl.node %48 : !firrtl.uint<1>
  %49 = firrtl.or %_cs_2_T_4, %_cs_2_T_6 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_2_T_7 = firrtl.node %49 : !firrtl.uint<1>
  firrtl.strictconnect %cs_1_2, %_cs_2_T_7 : !firrtl.uint<1>
  %50 = firrtl.bits %g_1 2 to 2 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_3_T_4 = firrtl.node %50 : !firrtl.uint<1>
  %51 = firrtl.bits %p_1 2 to 2 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_3_T_5 = firrtl.node %51 : !firrtl.uint<1>
  %52 = firrtl.and %_cs_3_T_5, %cs_1_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_3_T_6 = firrtl.node %52 : !firrtl.uint<1>
  %53 = firrtl.or %_cs_3_T_4, %_cs_3_T_6 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_3_T_7 = firrtl.node %53 : !firrtl.uint<1>
  firrtl.strictconnect %cs_1_3, %_cs_3_T_7 : !firrtl.uint<1>
  %54 = firrtl.bits %g_1 3 to 3 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_4_T_4 = firrtl.node %54 : !firrtl.uint<1>
  %55 = firrtl.bits %p_1 3 to 3 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_4_T_5 = firrtl.node %55 : !firrtl.uint<1>
  %56 = firrtl.and %_cs_4_T_5, %cs_1_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_4_T_6 = firrtl.node %56 : !firrtl.uint<1>
  %57 = firrtl.or %_cs_4_T_4, %_cs_4_T_6 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_4_T_7 = firrtl.node %57 : !firrtl.uint<1>
  firrtl.strictconnect %cs_1_4, %_cs_4_T_7 : !firrtl.uint<1>
  %58 = firrtl.cat %cs_1_1, %cs_1_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %res_1_lo = firrtl.node %58 : !firrtl.uint<2>
  %59 = firrtl.cat %cs_1_4, %cs_1_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %res_1_hi_hi = firrtl.node %59 : !firrtl.uint<2>
  %60 = firrtl.cat %res_1_hi_hi, %cs_1_2 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<3>
  %res_1_hi = firrtl.node %60 : !firrtl.uint<3>
  %61 = firrtl.cat %res_1_hi, %res_1_lo : (!firrtl.uint<3>, !firrtl.uint<2>) -> !firrtl.uint<5>
  %_res_1_T = firrtl.node %61 : !firrtl.uint<5>
  %62 = firrtl.bits %_res_1_T 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_1_T_1 = firrtl.node %62 : !firrtl.uint<4>
  %63 = firrtl.xor %p_1, %_res_1_T_1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_res_1_T_2 = firrtl.node %63 : !firrtl.uint<4>
  firrtl.strictconnect %res_1, %_res_1_T_2 : !firrtl.uint<4>
  firrtl.strictconnect %couts_2, %cs_1_4 : !firrtl.uint<1>
  %64 = firrtl.xor %aOp_2, %bOp_2 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %p_2 = firrtl.node %64 : !firrtl.uint<4>
  %65 = firrtl.and %aOp_2, %bOp_2 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %g_2 = firrtl.node %65 : !firrtl.uint<4>
  %cs_2_0 = firrtl.wire : !firrtl.uint<1>
  %cs_2_1 = firrtl.wire : !firrtl.uint<1>
  %cs_2_2 = firrtl.wire : !firrtl.uint<1>
  %cs_2_3 = firrtl.wire : !firrtl.uint<1>
  %cs_2_4 = firrtl.wire : !firrtl.uint<1>
  firrtl.strictconnect %cs_2_0, %couts_2 : !firrtl.uint<1>
  %66 = firrtl.bits %g_2 0 to 0 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_1_T_8 = firrtl.node %66 : !firrtl.uint<1>
  %67 = firrtl.bits %p_2 0 to 0 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_1_T_9 = firrtl.node %67 : !firrtl.uint<1>
  %68 = firrtl.and %_cs_1_T_9, %cs_2_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_1_T_10 = firrtl.node %68 : !firrtl.uint<1>
  %69 = firrtl.or %_cs_1_T_8, %_cs_1_T_10 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_1_T_11 = firrtl.node %69 : !firrtl.uint<1>
  firrtl.strictconnect %cs_2_1, %_cs_1_T_11 : !firrtl.uint<1>
  %70 = firrtl.bits %g_2 1 to 1 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_2_T_8 = firrtl.node %70 : !firrtl.uint<1>
  %71 = firrtl.bits %p_2 1 to 1 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_2_T_9 = firrtl.node %71 : !firrtl.uint<1>
  %72 = firrtl.and %_cs_2_T_9, %cs_2_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_2_T_10 = firrtl.node %72 : !firrtl.uint<1>
  %73 = firrtl.or %_cs_2_T_8, %_cs_2_T_10 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_2_T_11 = firrtl.node %73 : !firrtl.uint<1>
  firrtl.strictconnect %cs_2_2, %_cs_2_T_11 : !firrtl.uint<1>
  %74 = firrtl.bits %g_2 2 to 2 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_3_T_8 = firrtl.node %74 : !firrtl.uint<1>
  %75 = firrtl.bits %p_2 2 to 2 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_3_T_9 = firrtl.node %75 : !firrtl.uint<1>
  %76 = firrtl.and %_cs_3_T_9, %cs_2_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_3_T_10 = firrtl.node %76 : !firrtl.uint<1>
  %77 = firrtl.or %_cs_3_T_8, %_cs_3_T_10 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_3_T_11 = firrtl.node %77 : !firrtl.uint<1>
  firrtl.strictconnect %cs_2_3, %_cs_3_T_11 : !firrtl.uint<1>
  %78 = firrtl.bits %g_2 3 to 3 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_4_T_8 = firrtl.node %78 : !firrtl.uint<1>
  %79 = firrtl.bits %p_2 3 to 3 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_4_T_9 = firrtl.node %79 : !firrtl.uint<1>
  %80 = firrtl.and %_cs_4_T_9, %cs_2_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_4_T_10 = firrtl.node %80 : !firrtl.uint<1>
  %81 = firrtl.or %_cs_4_T_8, %_cs_4_T_10 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_4_T_11 = firrtl.node %81 : !firrtl.uint<1>
  firrtl.strictconnect %cs_2_4, %_cs_4_T_11 : !firrtl.uint<1>
  %82 = firrtl.cat %cs_2_1, %cs_2_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %res_2_lo = firrtl.node %82 : !firrtl.uint<2>
  %83 = firrtl.cat %cs_2_4, %cs_2_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %res_2_hi_hi = firrtl.node %83 : !firrtl.uint<2>
  %84 = firrtl.cat %res_2_hi_hi, %cs_2_2 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<3>
  %res_2_hi = firrtl.node %84 : !firrtl.uint<3>
  %85 = firrtl.cat %res_2_hi, %res_2_lo : (!firrtl.uint<3>, !firrtl.uint<2>) -> !firrtl.uint<5>
  %_res_2_T = firrtl.node %85 : !firrtl.uint<5>
  %86 = firrtl.bits %_res_2_T 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_2_T_1 = firrtl.node %86 : !firrtl.uint<4>
  %87 = firrtl.xor %p_2, %_res_2_T_1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_res_2_T_2 = firrtl.node %87 : !firrtl.uint<4>
  firrtl.strictconnect %res_2, %_res_2_T_2 : !firrtl.uint<4>
  firrtl.strictconnect %couts_3, %cs_2_4 : !firrtl.uint<1>
  %88 = firrtl.xor %aOp_3, %bOp_3 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %p_3 = firrtl.node %88 : !firrtl.uint<4>
  %89 = firrtl.and %aOp_3, %bOp_3 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %g_3 = firrtl.node %89 : !firrtl.uint<4>
  %cs_3_0 = firrtl.wire : !firrtl.uint<1>
  %cs_3_1 = firrtl.wire : !firrtl.uint<1>
  %cs_3_2 = firrtl.wire : !firrtl.uint<1>
  %cs_3_3 = firrtl.wire : !firrtl.uint<1>
  %cs_3_4 = firrtl.wire : !firrtl.uint<1>
  firrtl.strictconnect %cs_3_0, %couts_3 : !firrtl.uint<1>
  %90 = firrtl.bits %g_3 0 to 0 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_1_T_12 = firrtl.node %90 : !firrtl.uint<1>
  %91 = firrtl.bits %p_3 0 to 0 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_1_T_13 = firrtl.node %91 : !firrtl.uint<1>
  %92 = firrtl.and %_cs_1_T_13, %cs_3_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_1_T_14 = firrtl.node %92 : !firrtl.uint<1>
  %93 = firrtl.or %_cs_1_T_12, %_cs_1_T_14 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_1_T_15 = firrtl.node %93 : !firrtl.uint<1>
  firrtl.strictconnect %cs_3_1, %_cs_1_T_15 : !firrtl.uint<1>
  %94 = firrtl.bits %g_3 1 to 1 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_2_T_12 = firrtl.node %94 : !firrtl.uint<1>
  %95 = firrtl.bits %p_3 1 to 1 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_2_T_13 = firrtl.node %95 : !firrtl.uint<1>
  %96 = firrtl.and %_cs_2_T_13, %cs_3_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_2_T_14 = firrtl.node %96 : !firrtl.uint<1>
  %97 = firrtl.or %_cs_2_T_12, %_cs_2_T_14 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_2_T_15 = firrtl.node %97 : !firrtl.uint<1>
  firrtl.strictconnect %cs_3_2, %_cs_2_T_15 : !firrtl.uint<1>
  %98 = firrtl.bits %g_3 2 to 2 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_3_T_12 = firrtl.node %98 : !firrtl.uint<1>
  %99 = firrtl.bits %p_3 2 to 2 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_3_T_13 = firrtl.node %99 : !firrtl.uint<1>
  %100 = firrtl.and %_cs_3_T_13, %cs_3_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_3_T_14 = firrtl.node %100 : !firrtl.uint<1>
  %101 = firrtl.or %_cs_3_T_12, %_cs_3_T_14 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_3_T_15 = firrtl.node %101 : !firrtl.uint<1>
  firrtl.strictconnect %cs_3_3, %_cs_3_T_15 : !firrtl.uint<1>
  %102 = firrtl.bits %g_3 3 to 3 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_4_T_12 = firrtl.node %102 : !firrtl.uint<1>
  %103 = firrtl.bits %p_3 3 to 3 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_4_T_13 = firrtl.node %103 : !firrtl.uint<1>
  %104 = firrtl.and %_cs_4_T_13, %cs_3_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_4_T_14 = firrtl.node %104 : !firrtl.uint<1>
  %105 = firrtl.or %_cs_4_T_12, %_cs_4_T_14 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_4_T_15 = firrtl.node %105 : !firrtl.uint<1>
  firrtl.strictconnect %cs_3_4, %_cs_4_T_15 : !firrtl.uint<1>
  %106 = firrtl.cat %cs_3_1, %cs_3_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %res_3_lo = firrtl.node %106 : !firrtl.uint<2>
  %107 = firrtl.cat %cs_3_4, %cs_3_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %res_3_hi_hi = firrtl.node %107 : !firrtl.uint<2>
  %108 = firrtl.cat %res_3_hi_hi, %cs_3_2 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<3>
  %res_3_hi = firrtl.node %108 : !firrtl.uint<3>
  %109 = firrtl.cat %res_3_hi, %res_3_lo : (!firrtl.uint<3>, !firrtl.uint<2>) -> !firrtl.uint<5>
  %_res_3_T = firrtl.node %109 : !firrtl.uint<5>
  %110 = firrtl.bits %_res_3_T 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_3_T_1 = firrtl.node %110 : !firrtl.uint<4>
  %111 = firrtl.xor %p_3, %_res_3_T_1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_res_3_T_2 = firrtl.node %111 : !firrtl.uint<4>
  firrtl.strictconnect %res_3, %_res_3_T_2 : !firrtl.uint<4>
  firrtl.strictconnect %couts_4, %cs_3_4 : !firrtl.uint<1>
  %112 = firrtl.xor %aOp_4, %bOp_4 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %p_4 = firrtl.node %112 : !firrtl.uint<4>
  %113 = firrtl.and %aOp_4, %bOp_4 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %g_4 = firrtl.node %113 : !firrtl.uint<4>
  %cs_4_0 = firrtl.wire : !firrtl.uint<1>
  %cs_4_1 = firrtl.wire : !firrtl.uint<1>
  %cs_4_2 = firrtl.wire : !firrtl.uint<1>
  %cs_4_3 = firrtl.wire : !firrtl.uint<1>
  %cs_4_4 = firrtl.wire : !firrtl.uint<1>
  firrtl.strictconnect %cs_4_0, %couts_4 : !firrtl.uint<1>
  %114 = firrtl.bits %g_4 0 to 0 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_1_T_16 = firrtl.node %114 : !firrtl.uint<1>
  %115 = firrtl.bits %p_4 0 to 0 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_1_T_17 = firrtl.node %115 : !firrtl.uint<1>
  %116 = firrtl.and %_cs_1_T_17, %cs_4_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_1_T_18 = firrtl.node %116 : !firrtl.uint<1>
  %117 = firrtl.or %_cs_1_T_16, %_cs_1_T_18 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_1_T_19 = firrtl.node %117 : !firrtl.uint<1>
  firrtl.strictconnect %cs_4_1, %_cs_1_T_19 : !firrtl.uint<1>
  %118 = firrtl.bits %g_4 1 to 1 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_2_T_16 = firrtl.node %118 : !firrtl.uint<1>
  %119 = firrtl.bits %p_4 1 to 1 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_2_T_17 = firrtl.node %119 : !firrtl.uint<1>
  %120 = firrtl.and %_cs_2_T_17, %cs_4_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_2_T_18 = firrtl.node %120 : !firrtl.uint<1>
  %121 = firrtl.or %_cs_2_T_16, %_cs_2_T_18 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_2_T_19 = firrtl.node %121 : !firrtl.uint<1>
  firrtl.strictconnect %cs_4_2, %_cs_2_T_19 : !firrtl.uint<1>
  %122 = firrtl.bits %g_4 2 to 2 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_3_T_16 = firrtl.node %122 : !firrtl.uint<1>
  %123 = firrtl.bits %p_4 2 to 2 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_3_T_17 = firrtl.node %123 : !firrtl.uint<1>
  %124 = firrtl.and %_cs_3_T_17, %cs_4_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_3_T_18 = firrtl.node %124 : !firrtl.uint<1>
  %125 = firrtl.or %_cs_3_T_16, %_cs_3_T_18 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_3_T_19 = firrtl.node %125 : !firrtl.uint<1>
  firrtl.strictconnect %cs_4_3, %_cs_3_T_19 : !firrtl.uint<1>
  %126 = firrtl.bits %g_4 3 to 3 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_4_T_16 = firrtl.node %126 : !firrtl.uint<1>
  %127 = firrtl.bits %p_4 3 to 3 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_4_T_17 = firrtl.node %127 : !firrtl.uint<1>
  %128 = firrtl.and %_cs_4_T_17, %cs_4_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_4_T_18 = firrtl.node %128 : !firrtl.uint<1>
  %129 = firrtl.or %_cs_4_T_16, %_cs_4_T_18 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_4_T_19 = firrtl.node %129 : !firrtl.uint<1>
  firrtl.strictconnect %cs_4_4, %_cs_4_T_19 : !firrtl.uint<1>
  %130 = firrtl.cat %cs_4_1, %cs_4_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %res_4_lo = firrtl.node %130 : !firrtl.uint<2>
  %131 = firrtl.cat %cs_4_4, %cs_4_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %res_4_hi_hi = firrtl.node %131 : !firrtl.uint<2>
  %132 = firrtl.cat %res_4_hi_hi, %cs_4_2 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<3>
  %res_4_hi = firrtl.node %132 : !firrtl.uint<3>
  %133 = firrtl.cat %res_4_hi, %res_4_lo : (!firrtl.uint<3>, !firrtl.uint<2>) -> !firrtl.uint<5>
  %_res_4_T = firrtl.node %133 : !firrtl.uint<5>
  %134 = firrtl.bits %_res_4_T 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_4_T_1 = firrtl.node %134 : !firrtl.uint<4>
  %135 = firrtl.xor %p_4, %_res_4_T_1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_res_4_T_2 = firrtl.node %135 : !firrtl.uint<4>
  firrtl.strictconnect %res_4, %_res_4_T_2 : !firrtl.uint<4>
  firrtl.strictconnect %couts_5, %cs_4_4 : !firrtl.uint<1>
  %136 = firrtl.xor %aOp_5, %bOp_5 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %p_5 = firrtl.node %136 : !firrtl.uint<4>
  %137 = firrtl.and %aOp_5, %bOp_5 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %g_5 = firrtl.node %137 : !firrtl.uint<4>
  %cs_5_0 = firrtl.wire : !firrtl.uint<1>
  %cs_5_1 = firrtl.wire : !firrtl.uint<1>
  %cs_5_2 = firrtl.wire : !firrtl.uint<1>
  %cs_5_3 = firrtl.wire : !firrtl.uint<1>
  %cs_5_4 = firrtl.wire : !firrtl.uint<1>
  firrtl.strictconnect %cs_5_0, %couts_5 : !firrtl.uint<1>
  %138 = firrtl.bits %g_5 0 to 0 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_1_T_20 = firrtl.node %138 : !firrtl.uint<1>
  %139 = firrtl.bits %p_5 0 to 0 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_1_T_21 = firrtl.node %139 : !firrtl.uint<1>
  %140 = firrtl.and %_cs_1_T_21, %cs_5_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_1_T_22 = firrtl.node %140 : !firrtl.uint<1>
  %141 = firrtl.or %_cs_1_T_20, %_cs_1_T_22 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_1_T_23 = firrtl.node %141 : !firrtl.uint<1>
  firrtl.strictconnect %cs_5_1, %_cs_1_T_23 : !firrtl.uint<1>
  %142 = firrtl.bits %g_5 1 to 1 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_2_T_20 = firrtl.node %142 : !firrtl.uint<1>
  %143 = firrtl.bits %p_5 1 to 1 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_2_T_21 = firrtl.node %143 : !firrtl.uint<1>
  %144 = firrtl.and %_cs_2_T_21, %cs_5_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_2_T_22 = firrtl.node %144 : !firrtl.uint<1>
  %145 = firrtl.or %_cs_2_T_20, %_cs_2_T_22 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_2_T_23 = firrtl.node %145 : !firrtl.uint<1>
  firrtl.strictconnect %cs_5_2, %_cs_2_T_23 : !firrtl.uint<1>
  %146 = firrtl.bits %g_5 2 to 2 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_3_T_20 = firrtl.node %146 : !firrtl.uint<1>
  %147 = firrtl.bits %p_5 2 to 2 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_3_T_21 = firrtl.node %147 : !firrtl.uint<1>
  %148 = firrtl.and %_cs_3_T_21, %cs_5_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_3_T_22 = firrtl.node %148 : !firrtl.uint<1>
  %149 = firrtl.or %_cs_3_T_20, %_cs_3_T_22 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_3_T_23 = firrtl.node %149 : !firrtl.uint<1>
  firrtl.strictconnect %cs_5_3, %_cs_3_T_23 : !firrtl.uint<1>
  %150 = firrtl.bits %g_5 3 to 3 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_4_T_20 = firrtl.node %150 : !firrtl.uint<1>
  %151 = firrtl.bits %p_5 3 to 3 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_4_T_21 = firrtl.node %151 : !firrtl.uint<1>
  %152 = firrtl.and %_cs_4_T_21, %cs_5_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_4_T_22 = firrtl.node %152 : !firrtl.uint<1>
  %153 = firrtl.or %_cs_4_T_20, %_cs_4_T_22 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_4_T_23 = firrtl.node %153 : !firrtl.uint<1>
  firrtl.strictconnect %cs_5_4, %_cs_4_T_23 : !firrtl.uint<1>
  %154 = firrtl.cat %cs_5_1, %cs_5_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %res_5_lo = firrtl.node %154 : !firrtl.uint<2>
  %155 = firrtl.cat %cs_5_4, %cs_5_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %res_5_hi_hi = firrtl.node %155 : !firrtl.uint<2>
  %156 = firrtl.cat %res_5_hi_hi, %cs_5_2 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<3>
  %res_5_hi = firrtl.node %156 : !firrtl.uint<3>
  %157 = firrtl.cat %res_5_hi, %res_5_lo : (!firrtl.uint<3>, !firrtl.uint<2>) -> !firrtl.uint<5>
  %_res_5_T = firrtl.node %157 : !firrtl.uint<5>
  %158 = firrtl.bits %_res_5_T 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_5_T_1 = firrtl.node %158 : !firrtl.uint<4>
  %159 = firrtl.xor %p_5, %_res_5_T_1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_res_5_T_2 = firrtl.node %159 : !firrtl.uint<4>
  firrtl.strictconnect %res_5, %_res_5_T_2 : !firrtl.uint<4>
  firrtl.strictconnect %couts_6, %cs_5_4 : !firrtl.uint<1>
  %160 = firrtl.xor %aOp_6, %bOp_6 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %p_6 = firrtl.node %160 : !firrtl.uint<4>
  %161 = firrtl.and %aOp_6, %bOp_6 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %g_6 = firrtl.node %161 : !firrtl.uint<4>
  %cs_6_0 = firrtl.wire : !firrtl.uint<1>
  %cs_6_1 = firrtl.wire : !firrtl.uint<1>
  %cs_6_2 = firrtl.wire : !firrtl.uint<1>
  %cs_6_3 = firrtl.wire : !firrtl.uint<1>
  %cs_6_4 = firrtl.wire : !firrtl.uint<1>
  firrtl.strictconnect %cs_6_0, %couts_6 : !firrtl.uint<1>
  %162 = firrtl.bits %g_6 0 to 0 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_1_T_24 = firrtl.node %162 : !firrtl.uint<1>
  %163 = firrtl.bits %p_6 0 to 0 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_1_T_25 = firrtl.node %163 : !firrtl.uint<1>
  %164 = firrtl.and %_cs_1_T_25, %cs_6_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_1_T_26 = firrtl.node %164 : !firrtl.uint<1>
  %165 = firrtl.or %_cs_1_T_24, %_cs_1_T_26 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_1_T_27 = firrtl.node %165 : !firrtl.uint<1>
  firrtl.strictconnect %cs_6_1, %_cs_1_T_27 : !firrtl.uint<1>
  %166 = firrtl.bits %g_6 1 to 1 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_2_T_24 = firrtl.node %166 : !firrtl.uint<1>
  %167 = firrtl.bits %p_6 1 to 1 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_2_T_25 = firrtl.node %167 : !firrtl.uint<1>
  %168 = firrtl.and %_cs_2_T_25, %cs_6_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_2_T_26 = firrtl.node %168 : !firrtl.uint<1>
  %169 = firrtl.or %_cs_2_T_24, %_cs_2_T_26 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_2_T_27 = firrtl.node %169 : !firrtl.uint<1>
  firrtl.strictconnect %cs_6_2, %_cs_2_T_27 : !firrtl.uint<1>
  %170 = firrtl.bits %g_6 2 to 2 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_3_T_24 = firrtl.node %170 : !firrtl.uint<1>
  %171 = firrtl.bits %p_6 2 to 2 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_3_T_25 = firrtl.node %171 : !firrtl.uint<1>
  %172 = firrtl.and %_cs_3_T_25, %cs_6_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_3_T_26 = firrtl.node %172 : !firrtl.uint<1>
  %173 = firrtl.or %_cs_3_T_24, %_cs_3_T_26 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_3_T_27 = firrtl.node %173 : !firrtl.uint<1>
  firrtl.strictconnect %cs_6_3, %_cs_3_T_27 : !firrtl.uint<1>
  %174 = firrtl.bits %g_6 3 to 3 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_4_T_24 = firrtl.node %174 : !firrtl.uint<1>
  %175 = firrtl.bits %p_6 3 to 3 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_4_T_25 = firrtl.node %175 : !firrtl.uint<1>
  %176 = firrtl.and %_cs_4_T_25, %cs_6_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_4_T_26 = firrtl.node %176 : !firrtl.uint<1>
  %177 = firrtl.or %_cs_4_T_24, %_cs_4_T_26 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_4_T_27 = firrtl.node %177 : !firrtl.uint<1>
  firrtl.strictconnect %cs_6_4, %_cs_4_T_27 : !firrtl.uint<1>
  %178 = firrtl.cat %cs_6_1, %cs_6_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %res_6_lo = firrtl.node %178 : !firrtl.uint<2>
  %179 = firrtl.cat %cs_6_4, %cs_6_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %res_6_hi_hi = firrtl.node %179 : !firrtl.uint<2>
  %180 = firrtl.cat %res_6_hi_hi, %cs_6_2 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<3>
  %res_6_hi = firrtl.node %180 : !firrtl.uint<3>
  %181 = firrtl.cat %res_6_hi, %res_6_lo : (!firrtl.uint<3>, !firrtl.uint<2>) -> !firrtl.uint<5>
  %_res_6_T = firrtl.node %181 : !firrtl.uint<5>
  %182 = firrtl.bits %_res_6_T 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_6_T_1 = firrtl.node %182 : !firrtl.uint<4>
  %183 = firrtl.xor %p_6, %_res_6_T_1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_res_6_T_2 = firrtl.node %183 : !firrtl.uint<4>
  firrtl.strictconnect %res_6, %_res_6_T_2 : !firrtl.uint<4>
  firrtl.strictconnect %couts_7, %cs_6_4 : !firrtl.uint<1>
  %184 = firrtl.xor %aOp_7, %bOp_7 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %p_7 = firrtl.node %184 : !firrtl.uint<4>
  %185 = firrtl.and %aOp_7, %bOp_7 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %g_7 = firrtl.node %185 : !firrtl.uint<4>
  %cs_7_0 = firrtl.wire : !firrtl.uint<1>
  %cs_7_1 = firrtl.wire : !firrtl.uint<1>
  %cs_7_2 = firrtl.wire : !firrtl.uint<1>
  %cs_7_3 = firrtl.wire : !firrtl.uint<1>
  %cs_7_4 = firrtl.wire : !firrtl.uint<1>
  firrtl.strictconnect %cs_7_0, %couts_7 : !firrtl.uint<1>
  %186 = firrtl.bits %g_7 0 to 0 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_1_T_28 = firrtl.node %186 : !firrtl.uint<1>
  %187 = firrtl.bits %p_7 0 to 0 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_1_T_29 = firrtl.node %187 : !firrtl.uint<1>
  %188 = firrtl.and %_cs_1_T_29, %cs_7_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_1_T_30 = firrtl.node %188 : !firrtl.uint<1>
  %189 = firrtl.or %_cs_1_T_28, %_cs_1_T_30 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_1_T_31 = firrtl.node %189 : !firrtl.uint<1>
  firrtl.strictconnect %cs_7_1, %_cs_1_T_31 : !firrtl.uint<1>
  %190 = firrtl.bits %g_7 1 to 1 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_2_T_28 = firrtl.node %190 : !firrtl.uint<1>
  %191 = firrtl.bits %p_7 1 to 1 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_2_T_29 = firrtl.node %191 : !firrtl.uint<1>
  %192 = firrtl.and %_cs_2_T_29, %cs_7_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_2_T_30 = firrtl.node %192 : !firrtl.uint<1>
  %193 = firrtl.or %_cs_2_T_28, %_cs_2_T_30 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_2_T_31 = firrtl.node %193 : !firrtl.uint<1>
  firrtl.strictconnect %cs_7_2, %_cs_2_T_31 : !firrtl.uint<1>
  %194 = firrtl.bits %g_7 2 to 2 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_3_T_28 = firrtl.node %194 : !firrtl.uint<1>
  %195 = firrtl.bits %p_7 2 to 2 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_3_T_29 = firrtl.node %195 : !firrtl.uint<1>
  %196 = firrtl.and %_cs_3_T_29, %cs_7_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_3_T_30 = firrtl.node %196 : !firrtl.uint<1>
  %197 = firrtl.or %_cs_3_T_28, %_cs_3_T_30 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_3_T_31 = firrtl.node %197 : !firrtl.uint<1>
  firrtl.strictconnect %cs_7_3, %_cs_3_T_31 : !firrtl.uint<1>
  %198 = firrtl.bits %g_7 3 to 3 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_4_T_28 = firrtl.node %198 : !firrtl.uint<1>
  %199 = firrtl.bits %p_7 3 to 3 : (!firrtl.uint<4>) -> !firrtl.uint<1>
  %_cs_4_T_29 = firrtl.node %199 : !firrtl.uint<1>
  %200 = firrtl.and %_cs_4_T_29, %cs_7_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_4_T_30 = firrtl.node %200 : !firrtl.uint<1>
  %201 = firrtl.or %_cs_4_T_28, %_cs_4_T_30 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cs_4_T_31 = firrtl.node %201 : !firrtl.uint<1>
  firrtl.strictconnect %cs_7_4, %_cs_4_T_31 : !firrtl.uint<1>
  %202 = firrtl.cat %cs_7_1, %cs_7_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %res_7_lo = firrtl.node %202 : !firrtl.uint<2>
  %203 = firrtl.cat %cs_7_4, %cs_7_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %res_7_hi_hi = firrtl.node %203 : !firrtl.uint<2>
  %204 = firrtl.cat %res_7_hi_hi, %cs_7_2 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<3>
  %res_7_hi = firrtl.node %204 : !firrtl.uint<3>
  %205 = firrtl.cat %res_7_hi, %res_7_lo : (!firrtl.uint<3>, !firrtl.uint<2>) -> !firrtl.uint<5>
  %_res_7_T = firrtl.node %205 : !firrtl.uint<5>
  %206 = firrtl.bits %_res_7_T 3 to 0 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_res_7_T_1 = firrtl.node %206 : !firrtl.uint<4>
  %207 = firrtl.xor %p_7, %_res_7_T_1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_res_7_T_2 = firrtl.node %207 : !firrtl.uint<4>
  firrtl.strictconnect %res_7, %_res_7_T_2 : !firrtl.uint<4>
  firrtl.strictconnect %couts_8, %cs_7_4 : !firrtl.uint<1>
  %208 = firrtl.cat %res_1, %res_0 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>
  %io_c_lo_lo = firrtl.node %208 : !firrtl.uint<8>
  %209 = firrtl.cat %res_3, %res_2 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>
  %io_c_lo_hi = firrtl.node %209 : !firrtl.uint<8>
  %210 = firrtl.cat %io_c_lo_hi, %io_c_lo_lo : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<16>
  %io_c_lo = firrtl.node %210 : !firrtl.uint<16>
  %211 = firrtl.cat %res_5, %res_4 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>
  %io_c_hi_lo = firrtl.node %211 : !firrtl.uint<8>
  %212 = firrtl.cat %res_7, %res_6 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>
  %io_c_hi_hi = firrtl.node %212 : !firrtl.uint<8>
  %213 = firrtl.cat %io_c_hi_hi, %io_c_hi_lo : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<16>
  %io_c_hi = firrtl.node %213 : !firrtl.uint<16>
  %214 = firrtl.cat %io_c_hi, %io_c_lo : (!firrtl.uint<16>, !firrtl.uint<16>) -> !firrtl.uint<32>
  %_io_c_T = firrtl.node %214 : !firrtl.uint<32>
  %215 = firrtl.bits %_io_c_T 31 to 0 : (!firrtl.uint<32>) -> !firrtl.uint<32>
  %_io_c_T_1 = firrtl.node %215 : !firrtl.uint<32>
  firrtl.strictconnect %io_c_3, %_io_c_T_1 : !firrtl.uint<32>
  firrtl.strictconnect %io_cout_4, %couts_8 : !firrtl.uint<1>
}

