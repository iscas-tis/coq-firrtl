// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @FunctionalMin(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %io_in_0: !firrtl.uint<8>, in %io_in_1: !firrtl.uint<8>, in %io_in_2: !firrtl.uint<8>, in %io_in_3: !firrtl.uint<8>, in %io_in_4: !firrtl.uint<8>, out %io_min: !firrtl.uint<8>, out %io_resA: !firrtl.uint<8>, out %io_idxA: !firrtl.uint<8>, out %io_resB: !firrtl.uint<8>, out %io_idxB: !firrtl.uint<8>, out %io_resC: !firrtl.uint<8>, out %io_idxC: !firrtl.uint<8>) attributes {convention = #firrtl<convention scalarized>} {
  %io_in_0_0 = firrtl.wire {name = "io_in_0"} : !firrtl.uint<8>
  %io_in_1_1 = firrtl.wire {name = "io_in_1"} : !firrtl.uint<8>
  %io_in_2_2 = firrtl.wire {name = "io_in_2"} : !firrtl.uint<8>
  %io_in_3_3 = firrtl.wire {name = "io_in_3"} : !firrtl.uint<8>
  %io_in_4_4 = firrtl.wire {name = "io_in_4"} : !firrtl.uint<8>
  %io_min_5 = firrtl.wire {name = "io_min"} : !firrtl.uint<8>
  %io_resA_6 = firrtl.wire {name = "io_resA"} : !firrtl.uint<8>
  %io_idxA_7 = firrtl.wire {name = "io_idxA"} : !firrtl.uint<8>
  %io_resB_8 = firrtl.wire {name = "io_resB"} : !firrtl.uint<8>
  %io_idxB_9 = firrtl.wire {name = "io_idxB"} : !firrtl.uint<8>
  %io_resC_10 = firrtl.wire {name = "io_resC"} : !firrtl.uint<8>
  %io_idxC_11 = firrtl.wire {name = "io_idxC"} : !firrtl.uint<8>
  firrtl.strictconnect %io_in_0_0, %io_in_0 : !firrtl.uint<8>
  firrtl.strictconnect %io_in_1_1, %io_in_1 : !firrtl.uint<8>
  firrtl.strictconnect %io_in_2_2, %io_in_2 : !firrtl.uint<8>
  firrtl.strictconnect %io_in_3_3, %io_in_3 : !firrtl.uint<8>
  firrtl.strictconnect %io_in_4_4, %io_in_4 : !firrtl.uint<8>
  firrtl.strictconnect %io_min, %io_min_5 : !firrtl.uint<8>
  firrtl.strictconnect %io_resA, %io_resA_6 : !firrtl.uint<8>
  firrtl.strictconnect %io_idxA, %io_idxA_7 : !firrtl.uint<8>
  firrtl.strictconnect %io_resB, %io_resB_8 : !firrtl.uint<8>
  firrtl.strictconnect %io_idxB, %io_idxB_9 : !firrtl.uint<8>
  firrtl.strictconnect %io_resC, %io_resC_10 : !firrtl.uint<8>
  firrtl.strictconnect %io_idxC, %io_idxC_11 : !firrtl.uint<8>
  %0 = firrtl.lt %io_in_3_3, %io_in_4_4 : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<1>
  %_min_T = firrtl.node %0 : !firrtl.uint<1>
  %1 = firrtl.mux(%_min_T, %io_in_3_3, %io_in_4_4) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %_min_T_1 = firrtl.node %1 : !firrtl.uint<8>
  %2 = firrtl.lt %io_in_0_0, %io_in_1_1 : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<1>
  %_min_T_2 = firrtl.node %2 : !firrtl.uint<1>
  %3 = firrtl.mux(%_min_T_2, %io_in_0_0, %io_in_1_1) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %_min_T_3 = firrtl.node %3 : !firrtl.uint<8>
  %4 = firrtl.lt %io_in_2_2, %_min_T_1 : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<1>
  %_min_T_4 = firrtl.node %4 : !firrtl.uint<1>
  %5 = firrtl.mux(%_min_T_4, %io_in_2_2, %_min_T_1) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %_min_T_5 = firrtl.node %5 : !firrtl.uint<8>
  %6 = firrtl.lt %_min_T_3, %_min_T_5 : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<1>
  %_min_T_6 = firrtl.node %6 : !firrtl.uint<1>
  %7 = firrtl.mux(%_min_T_6, %_min_T_3, %_min_T_5) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %min = firrtl.node %7 : !firrtl.uint<8>
  %vecTwo_0_v = firrtl.wire : !firrtl.uint<8>
  %vecTwo_0_idx = firrtl.wire : !firrtl.uint<8>
  %vecTwo_1_v = firrtl.wire : !firrtl.uint<8>
  %vecTwo_1_idx = firrtl.wire : !firrtl.uint<8>
  %vecTwo_2_v = firrtl.wire : !firrtl.uint<8>
  %vecTwo_2_idx = firrtl.wire : !firrtl.uint<8>
  %vecTwo_3_v = firrtl.wire : !firrtl.uint<8>
  %vecTwo_3_idx = firrtl.wire : !firrtl.uint<8>
  %vecTwo_4_v = firrtl.wire : !firrtl.uint<8>
  %vecTwo_4_idx = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %vecTwo_0_v, %io_in_0_0 : !firrtl.uint<8>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %8 = firrtl.pad %c0_ui1, 8 : (!firrtl.uint<1>) -> !firrtl.uint<8>
  firrtl.strictconnect %vecTwo_0_idx, %8 : !firrtl.uint<8>
  firrtl.strictconnect %vecTwo_1_v, %io_in_1_1 : !firrtl.uint<8>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %9 = firrtl.pad %c1_ui1, 8 : (!firrtl.uint<1>) -> !firrtl.uint<8>
  firrtl.strictconnect %vecTwo_1_idx, %9 : !firrtl.uint<8>
  firrtl.strictconnect %vecTwo_2_v, %io_in_2_2 : !firrtl.uint<8>
  %c2_ui2 = firrtl.constant 2 : !firrtl.uint<2>
  %10 = firrtl.pad %c2_ui2, 8 : (!firrtl.uint<2>) -> !firrtl.uint<8>
  firrtl.strictconnect %vecTwo_2_idx, %10 : !firrtl.uint<8>
  firrtl.strictconnect %vecTwo_3_v, %io_in_3_3 : !firrtl.uint<8>
  %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
  %11 = firrtl.pad %c3_ui2, 8 : (!firrtl.uint<2>) -> !firrtl.uint<8>
  firrtl.strictconnect %vecTwo_3_idx, %11 : !firrtl.uint<8>
  firrtl.strictconnect %vecTwo_4_v, %io_in_4_4 : !firrtl.uint<8>
  %c4_ui3 = firrtl.constant 4 : !firrtl.uint<3>
  %12 = firrtl.pad %c4_ui3, 8 : (!firrtl.uint<3>) -> !firrtl.uint<8>
  firrtl.strictconnect %vecTwo_4_idx, %12 : !firrtl.uint<8>
  %13 = firrtl.lt %vecTwo_3_v, %vecTwo_4_v : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<1>
  %_res_T = firrtl.node %13 : !firrtl.uint<1>
  %14 = firrtl.mux(%_res_T, %vecTwo_3_v, %vecTwo_4_v) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %15 = firrtl.mux(%_res_T, %vecTwo_3_idx, %vecTwo_4_idx) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %_res_T_1_v = firrtl.node %14 : !firrtl.uint<8>
  %_res_T_1_idx = firrtl.node %15 : !firrtl.uint<8>
  %16 = firrtl.lt %vecTwo_0_v, %vecTwo_1_v : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<1>
  %_res_T_2 = firrtl.node %16 : !firrtl.uint<1>
  %17 = firrtl.mux(%_res_T_2, %vecTwo_0_v, %vecTwo_1_v) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %18 = firrtl.mux(%_res_T_2, %vecTwo_0_idx, %vecTwo_1_idx) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %_res_T_3_v = firrtl.node %17 : !firrtl.uint<8>
  %_res_T_3_idx = firrtl.node %18 : !firrtl.uint<8>
  %19 = firrtl.lt %vecTwo_2_v, %_res_T_1_v : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<1>
  %_res_T_4 = firrtl.node %19 : !firrtl.uint<1>
  %20 = firrtl.mux(%_res_T_4, %vecTwo_2_v, %_res_T_1_v) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %21 = firrtl.mux(%_res_T_4, %vecTwo_2_idx, %_res_T_1_idx) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %_res_T_5_v = firrtl.node %20 : !firrtl.uint<8>
  %_res_T_5_idx = firrtl.node %21 : !firrtl.uint<8>
  %22 = firrtl.lt %_res_T_3_v, %_res_T_5_v : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<1>
  %_res_T_6 = firrtl.node %22 : !firrtl.uint<1>
  %23 = firrtl.mux(%_res_T_6, %_res_T_3_v, %_res_T_5_v) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %24 = firrtl.mux(%_res_T_6, %_res_T_3_idx, %_res_T_5_idx) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %res_v = firrtl.node %23 : !firrtl.uint<8>
  %res_idx = firrtl.node %24 : !firrtl.uint<8>
  %25 = firrtl.node %2 : !firrtl.uint<1>
  %26 = firrtl.mux(%25, %io_in_0_0, %io_in_1_1) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %27 = firrtl.node %26 : !firrtl.uint<8>
  %28 = firrtl.node %2 : !firrtl.uint<1>
  %29 = firrtl.mux(%28, %c0_ui1, %c1_ui1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %30 = firrtl.node %29 : !firrtl.uint<1>
  %31 = firrtl.lt %27, %io_in_2_2 : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<1>
  %32 = firrtl.node %31 : !firrtl.uint<1>
  %33 = firrtl.mux(%32, %27, %io_in_2_2) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %34 = firrtl.node %33 : !firrtl.uint<8>
  %35 = firrtl.node %31 : !firrtl.uint<1>
  %36 = firrtl.mux(%35, %30, %c2_ui2) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %37 = firrtl.node %36 : !firrtl.uint<2>
  %38 = firrtl.lt %34, %io_in_3_3 : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<1>
  %39 = firrtl.node %38 : !firrtl.uint<1>
  %40 = firrtl.mux(%39, %34, %io_in_3_3) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %41 = firrtl.node %40 : !firrtl.uint<8>
  %42 = firrtl.node %38 : !firrtl.uint<1>
  %43 = firrtl.mux(%42, %37, %c3_ui2) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %44 = firrtl.node %43 : !firrtl.uint<2>
  %45 = firrtl.lt %41, %io_in_4_4 : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<1>
  %46 = firrtl.node %45 : !firrtl.uint<1>
  %47 = firrtl.mux(%46, %41, %io_in_4_4) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %48 = firrtl.node %47 : !firrtl.uint<8>
  %49 = firrtl.node %45 : !firrtl.uint<1>
  %50 = firrtl.mux(%49, %44, %c4_ui3) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %51 = firrtl.node %50 : !firrtl.uint<3>
  %scalaVector_0_1 = firrtl.wire : !firrtl.uint<8>
  %scalaVector_0_0 = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %scalaVector_0_0, %io_in_0_0 : !firrtl.uint<8>
  %c0_ui8 = firrtl.constant 0 : !firrtl.uint<8>
  firrtl.strictconnect %scalaVector_0_1, %c0_ui8 : !firrtl.uint<8>
  %scalaVector_1_1 = firrtl.wire : !firrtl.uint<8>
  %scalaVector_1_0 = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %scalaVector_1_0, %io_in_1_1 : !firrtl.uint<8>
  %c1_ui8 = firrtl.constant 1 : !firrtl.uint<8>
  firrtl.strictconnect %scalaVector_1_1, %c1_ui8 : !firrtl.uint<8>
  %scalaVector_2_1 = firrtl.wire : !firrtl.uint<8>
  %scalaVector_2_0 = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %scalaVector_2_0, %io_in_2_2 : !firrtl.uint<8>
  %c2_ui8 = firrtl.constant 2 : !firrtl.uint<8>
  firrtl.strictconnect %scalaVector_2_1, %c2_ui8 : !firrtl.uint<8>
  %scalaVector_3_1 = firrtl.wire : !firrtl.uint<8>
  %scalaVector_3_0 = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %scalaVector_3_0, %io_in_3_3 : !firrtl.uint<8>
  %c3_ui8 = firrtl.constant 3 : !firrtl.uint<8>
  firrtl.strictconnect %scalaVector_3_1, %c3_ui8 : !firrtl.uint<8>
  %scalaVector_4_1 = firrtl.wire : !firrtl.uint<8>
  %scalaVector_4_0 = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %scalaVector_4_0, %io_in_4_4 : !firrtl.uint<8>
  %c4_ui8 = firrtl.constant 4 : !firrtl.uint<8>
  firrtl.strictconnect %scalaVector_4_1, %c4_ui8 : !firrtl.uint<8>
  %resFun2_qual1_0_1 = firrtl.wire : !firrtl.uint<8>
  %resFun2_qual1_0_0 = firrtl.wire : !firrtl.uint<8>
  %resFun2_qual1_1_1 = firrtl.wire : !firrtl.uint<8>
  %resFun2_qual1_1_0 = firrtl.wire : !firrtl.uint<8>
  %resFun2_qual1_2_1 = firrtl.wire : !firrtl.uint<8>
  %resFun2_qual1_2_0 = firrtl.wire : !firrtl.uint<8>
  %resFun2_qual1_3_1 = firrtl.wire : !firrtl.uint<8>
  %resFun2_qual1_3_0 = firrtl.wire : !firrtl.uint<8>
  %resFun2_qual1_4_1 = firrtl.wire : !firrtl.uint<8>
  %resFun2_qual1_4_0 = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %resFun2_qual1_0_1, %scalaVector_0_1 : !firrtl.uint<8>
  firrtl.strictconnect %resFun2_qual1_0_0, %scalaVector_0_0 : !firrtl.uint<8>
  firrtl.strictconnect %resFun2_qual1_1_1, %scalaVector_1_1 : !firrtl.uint<8>
  firrtl.strictconnect %resFun2_qual1_1_0, %scalaVector_1_0 : !firrtl.uint<8>
  firrtl.strictconnect %resFun2_qual1_2_1, %scalaVector_2_1 : !firrtl.uint<8>
  firrtl.strictconnect %resFun2_qual1_2_0, %scalaVector_2_0 : !firrtl.uint<8>
  firrtl.strictconnect %resFun2_qual1_3_1, %scalaVector_3_1 : !firrtl.uint<8>
  firrtl.strictconnect %resFun2_qual1_3_0, %scalaVector_3_0 : !firrtl.uint<8>
  firrtl.strictconnect %resFun2_qual1_4_1, %scalaVector_4_1 : !firrtl.uint<8>
  firrtl.strictconnect %resFun2_qual1_4_0, %scalaVector_4_0 : !firrtl.uint<8>
  %52 = firrtl.lt %resFun2_qual1_3_0, %resFun2_qual1_4_0 : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<1>
  %_resFun2_T = firrtl.node %52 : !firrtl.uint<1>
  %53 = firrtl.mux(%_resFun2_T, %resFun2_qual1_3_1, %resFun2_qual1_4_1) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %54 = firrtl.mux(%_resFun2_T, %resFun2_qual1_3_0, %resFun2_qual1_4_0) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %_resFun2_T_1_1 = firrtl.node %53 : !firrtl.uint<8>
  %_resFun2_T_1_0 = firrtl.node %54 : !firrtl.uint<8>
  %55 = firrtl.lt %resFun2_qual1_0_0, %resFun2_qual1_1_0 : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<1>
  %_resFun2_T_2 = firrtl.node %55 : !firrtl.uint<1>
  %56 = firrtl.mux(%_resFun2_T_2, %resFun2_qual1_0_1, %resFun2_qual1_1_1) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %57 = firrtl.mux(%_resFun2_T_2, %resFun2_qual1_0_0, %resFun2_qual1_1_0) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %_resFun2_T_3_1 = firrtl.node %56 : !firrtl.uint<8>
  %_resFun2_T_3_0 = firrtl.node %57 : !firrtl.uint<8>
  %58 = firrtl.lt %resFun2_qual1_2_0, %_resFun2_T_1_0 : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<1>
  %_resFun2_T_4 = firrtl.node %58 : !firrtl.uint<1>
  %59 = firrtl.mux(%_resFun2_T_4, %resFun2_qual1_2_1, %_resFun2_T_1_1) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %60 = firrtl.mux(%_resFun2_T_4, %resFun2_qual1_2_0, %_resFun2_T_1_0) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %_resFun2_T_5_1 = firrtl.node %59 : !firrtl.uint<8>
  %_resFun2_T_5_0 = firrtl.node %60 : !firrtl.uint<8>
  %61 = firrtl.lt %_resFun2_T_3_0, %_resFun2_T_5_0 : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<1>
  %_resFun2_T_6 = firrtl.node %61 : !firrtl.uint<1>
  %62 = firrtl.mux(%_resFun2_T_6, %_resFun2_T_3_1, %_resFun2_T_5_1) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %63 = firrtl.mux(%_resFun2_T_6, %_resFun2_T_3_0, %_resFun2_T_5_0) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %resFun2_1 = firrtl.node %62 : !firrtl.uint<8>
  %resFun2_0 = firrtl.node %63 : !firrtl.uint<8>
  firrtl.strictconnect %io_min_5, %min : !firrtl.uint<8>
  firrtl.strictconnect %io_resA_6, %res_v : !firrtl.uint<8>
  firrtl.strictconnect %io_idxA_7, %res_idx : !firrtl.uint<8>
  firrtl.strictconnect %io_resB_8, %48 : !firrtl.uint<8>
  %64 = firrtl.pad %51, 8 : (!firrtl.uint<3>) -> !firrtl.uint<8>
  firrtl.strictconnect %io_idxB_9, %64 : !firrtl.uint<8>
  firrtl.strictconnect %io_resC_10, %resFun2_0 : !firrtl.uint<8>
  firrtl.strictconnect %io_idxC_11, %resFun2_1 : !firrtl.uint<8>
}

