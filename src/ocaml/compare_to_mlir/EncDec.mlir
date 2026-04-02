// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @EncDec(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %io_decin: !firrtl.uint<2>, out %io_decout: !firrtl.uint<4>, in %io_encin: !firrtl.uint<4>, out %io_encout: !firrtl.uint<2>, in %io_largeEncIn: !firrtl.uint<16>, out %io_largeEncOut: !firrtl.uint<4>) attributes {convention = #firrtl<convention scalarized>} {
  %io_decin_0 = firrtl.wire {name = "io_decin"} : !firrtl.uint<2>
  %io_decout_1 = firrtl.wire {name = "io_decout"} : !firrtl.uint<4>
  %io_encin_2 = firrtl.wire {name = "io_encin"} : !firrtl.uint<4>
  %io_encout_3 = firrtl.wire {name = "io_encout"} : !firrtl.uint<2>
  %io_largeEncIn_4 = firrtl.wire {name = "io_largeEncIn"} : !firrtl.uint<16>
  %io_largeEncOut_5 = firrtl.wire {name = "io_largeEncOut"} : !firrtl.uint<4>
  firrtl.strictconnect %io_decin_0, %io_decin : !firrtl.uint<2>
  firrtl.strictconnect %io_decout, %io_decout_1 : !firrtl.uint<4>
  firrtl.strictconnect %io_encin_2, %io_encin : !firrtl.uint<4>
  firrtl.strictconnect %io_encout, %io_encout_3 : !firrtl.uint<2>
  firrtl.strictconnect %io_largeEncIn_4, %io_largeEncIn : !firrtl.uint<16>
  firrtl.strictconnect %io_largeEncOut, %io_largeEncOut_5 : !firrtl.uint<4>
  %result = firrtl.wire : !firrtl.uint<4>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %0 = firrtl.pad %c0_ui1, 4 : (!firrtl.uint<1>) -> !firrtl.uint<4>
  %1 = firrtl.eq %c0_ui1, %io_decin_0 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %2 = firrtl.node %1 : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %c2_ui2 = firrtl.constant 2 : !firrtl.uint<2>
  %c4_ui3 = firrtl.constant 4 : !firrtl.uint<3>
  %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
  %c8_ui4 = firrtl.constant 8 : !firrtl.uint<4>
  %3 = firrtl.pad %c1_ui1, 4 : (!firrtl.uint<1>) -> !firrtl.uint<4>
  %4 = firrtl.not %2 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %5 = firrtl.eq %c1_ui1, %io_decin_0 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %6 = firrtl.node %5 : !firrtl.uint<1>
  %7 = firrtl.and %4, %6 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %8 = firrtl.pad %c2_ui2, 4 : (!firrtl.uint<2>) -> !firrtl.uint<4>
  %9 = firrtl.not %6 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %10 = firrtl.and %4, %9 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %11 = firrtl.eq %c2_ui2, %io_decin_0 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %12 = firrtl.node %11 : !firrtl.uint<1>
  %13 = firrtl.and %10, %12 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %14 = firrtl.pad %c4_ui3, 4 : (!firrtl.uint<3>) -> !firrtl.uint<4>
  %15 = firrtl.not %12 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %16 = firrtl.and %10, %15 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %17 = firrtl.eq %c3_ui2, %io_decin_0 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %18 = firrtl.node %17 : !firrtl.uint<1>
  %19 = firrtl.and %16, %18 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %20 = firrtl.mux(%18, %c8_ui4, %0) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %21 = firrtl.mux(%12, %14, %20) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %22 = firrtl.mux(%6, %8, %21) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %23 = firrtl.mux(%2, %3, %22) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %24 = firrtl.node %1 : !firrtl.uint<1>
  %25 = firrtl.pad %c1_ui1, 4 : (!firrtl.uint<1>) -> !firrtl.uint<4>
  %26 = firrtl.not %24 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %27 = firrtl.eq %c1_ui1, %io_decin_0 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %28 = firrtl.node %27 : !firrtl.uint<1>
  %29 = firrtl.and %26, %28 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %30 = firrtl.pad %c2_ui2, 4 : (!firrtl.uint<2>) -> !firrtl.uint<4>
  %31 = firrtl.not %28 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %32 = firrtl.and %26, %31 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %33 = firrtl.eq %c2_ui2, %io_decin_0 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %34 = firrtl.node %33 : !firrtl.uint<1>
  %35 = firrtl.and %32, %34 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %36 = firrtl.pad %c4_ui3, 4 : (!firrtl.uint<3>) -> !firrtl.uint<4>
  %37 = firrtl.not %34 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %38 = firrtl.and %32, %37 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %39 = firrtl.eq %c3_ui2, %io_decin_0 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %40 = firrtl.node %39 : !firrtl.uint<1>
  %41 = firrtl.and %38, %40 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %42 = firrtl.mux(%40, %c8_ui4, %23) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %43 = firrtl.mux(%34, %36, %42) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %44 = firrtl.mux(%28, %30, %43) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %45 = firrtl.mux(%24, %25, %44) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %46 = firrtl.dshl %c1_ui1, %io_decin_0 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<4>
  %_result_T = firrtl.node %46 : !firrtl.uint<4>
  firrtl.strictconnect %result, %_result_T : !firrtl.uint<4>
  firrtl.strictconnect %io_decout_1, %result : !firrtl.uint<4>
  %b = firrtl.wire : !firrtl.uint<2>
  %47 = firrtl.pad %c0_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %48 = firrtl.eq %c1_ui1, %io_encin_2 : (!firrtl.uint<1>, !firrtl.uint<4>) -> !firrtl.uint<1>
  %49 = firrtl.node %48 : !firrtl.uint<1>
  %50 = firrtl.not %49 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %51 = firrtl.eq %c2_ui2, %io_encin_2 : (!firrtl.uint<2>, !firrtl.uint<4>) -> !firrtl.uint<1>
  %52 = firrtl.node %51 : !firrtl.uint<1>
  %53 = firrtl.and %50, %52 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %54 = firrtl.pad %c1_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %55 = firrtl.not %52 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %56 = firrtl.and %50, %55 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %57 = firrtl.eq %c4_ui3, %io_encin_2 : (!firrtl.uint<3>, !firrtl.uint<4>) -> !firrtl.uint<1>
  %58 = firrtl.node %57 : !firrtl.uint<1>
  %59 = firrtl.and %56, %58 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %60 = firrtl.not %58 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %61 = firrtl.and %56, %60 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %62 = firrtl.eq %c8_ui4, %io_encin_2 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<1>
  %63 = firrtl.node %62 : !firrtl.uint<1>
  %64 = firrtl.and %61, %63 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %65 = firrtl.mux(%63, %c3_ui2, %47) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %66 = firrtl.mux(%58, %c2_ui2, %65) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %67 = firrtl.mux(%52, %54, %66) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %68 = firrtl.mux(%49, %47, %67) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  firrtl.connect %b, %68 : !firrtl.uint<2>, !firrtl.uint<2>
  firrtl.strictconnect %io_encout_3, %b : !firrtl.uint<2>
  %v_0 = firrtl.wire : !firrtl.uint<4>
  %v_1 = firrtl.wire : !firrtl.uint<4>
  %v_2 = firrtl.wire : !firrtl.uint<4>
  %v_3 = firrtl.wire : !firrtl.uint<4>
  %v_4 = firrtl.wire : !firrtl.uint<4>
  %v_5 = firrtl.wire : !firrtl.uint<4>
  %v_6 = firrtl.wire : !firrtl.uint<4>
  %v_7 = firrtl.wire : !firrtl.uint<4>
  %v_8 = firrtl.wire : !firrtl.uint<4>
  %v_9 = firrtl.wire : !firrtl.uint<4>
  %v_10 = firrtl.wire : !firrtl.uint<4>
  %v_11 = firrtl.wire : !firrtl.uint<4>
  %v_12 = firrtl.wire : !firrtl.uint<4>
  %v_13 = firrtl.wire : !firrtl.uint<4>
  %v_14 = firrtl.wire : !firrtl.uint<4>
  %v_15 = firrtl.wire : !firrtl.uint<4>
  firrtl.strictconnect %v_0, %0 : !firrtl.uint<4>
  %69 = firrtl.bits %io_largeEncIn_4 1 to 1 : (!firrtl.uint<16>) -> !firrtl.uint<1>
  %_v_1_T = firrtl.node %69 : !firrtl.uint<1>
  %70 = firrtl.mux(%_v_1_T, %c1_ui1, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_v_1_T_1 = firrtl.node %70 : !firrtl.uint<1>
  %71 = firrtl.or %_v_1_T_1, %v_0 : (!firrtl.uint<1>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_v_1_T_2 = firrtl.node %71 : !firrtl.uint<4>
  firrtl.strictconnect %v_1, %_v_1_T_2 : !firrtl.uint<4>
  %72 = firrtl.bits %io_largeEncIn_4 2 to 2 : (!firrtl.uint<16>) -> !firrtl.uint<1>
  %_v_2_T = firrtl.node %72 : !firrtl.uint<1>
  %73 = firrtl.mux(%_v_2_T, %c2_ui2, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %_v_2_T_1 = firrtl.node %73 : !firrtl.uint<2>
  %74 = firrtl.or %_v_2_T_1, %v_1 : (!firrtl.uint<2>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_v_2_T_2 = firrtl.node %74 : !firrtl.uint<4>
  firrtl.strictconnect %v_2, %_v_2_T_2 : !firrtl.uint<4>
  %75 = firrtl.bits %io_largeEncIn_4 3 to 3 : (!firrtl.uint<16>) -> !firrtl.uint<1>
  %_v_3_T = firrtl.node %75 : !firrtl.uint<1>
  %76 = firrtl.mux(%_v_3_T, %c3_ui2, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %_v_3_T_1 = firrtl.node %76 : !firrtl.uint<2>
  %77 = firrtl.or %_v_3_T_1, %v_2 : (!firrtl.uint<2>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_v_3_T_2 = firrtl.node %77 : !firrtl.uint<4>
  firrtl.strictconnect %v_3, %_v_3_T_2 : !firrtl.uint<4>
  %78 = firrtl.bits %io_largeEncIn_4 4 to 4 : (!firrtl.uint<16>) -> !firrtl.uint<1>
  %_v_4_T = firrtl.node %78 : !firrtl.uint<1>
  %79 = firrtl.mux(%_v_4_T, %c4_ui3, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<1>) -> !firrtl.uint<3>
  %_v_4_T_1 = firrtl.node %79 : !firrtl.uint<3>
  %80 = firrtl.or %_v_4_T_1, %v_3 : (!firrtl.uint<3>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_v_4_T_2 = firrtl.node %80 : !firrtl.uint<4>
  firrtl.strictconnect %v_4, %_v_4_T_2 : !firrtl.uint<4>
  %81 = firrtl.bits %io_largeEncIn_4 5 to 5 : (!firrtl.uint<16>) -> !firrtl.uint<1>
  %_v_5_T = firrtl.node %81 : !firrtl.uint<1>
  %c5_ui3 = firrtl.constant 5 : !firrtl.uint<3>
  %82 = firrtl.mux(%_v_5_T, %c5_ui3, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<1>) -> !firrtl.uint<3>
  %_v_5_T_1 = firrtl.node %82 : !firrtl.uint<3>
  %83 = firrtl.or %_v_5_T_1, %v_4 : (!firrtl.uint<3>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_v_5_T_2 = firrtl.node %83 : !firrtl.uint<4>
  firrtl.strictconnect %v_5, %_v_5_T_2 : !firrtl.uint<4>
  %84 = firrtl.bits %io_largeEncIn_4 6 to 6 : (!firrtl.uint<16>) -> !firrtl.uint<1>
  %_v_6_T = firrtl.node %84 : !firrtl.uint<1>
  %c6_ui3 = firrtl.constant 6 : !firrtl.uint<3>
  %85 = firrtl.mux(%_v_6_T, %c6_ui3, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<1>) -> !firrtl.uint<3>
  %_v_6_T_1 = firrtl.node %85 : !firrtl.uint<3>
  %86 = firrtl.or %_v_6_T_1, %v_5 : (!firrtl.uint<3>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_v_6_T_2 = firrtl.node %86 : !firrtl.uint<4>
  firrtl.strictconnect %v_6, %_v_6_T_2 : !firrtl.uint<4>
  %87 = firrtl.bits %io_largeEncIn_4 7 to 7 : (!firrtl.uint<16>) -> !firrtl.uint<1>
  %_v_7_T = firrtl.node %87 : !firrtl.uint<1>
  %c7_ui3 = firrtl.constant 7 : !firrtl.uint<3>
  %88 = firrtl.mux(%_v_7_T, %c7_ui3, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<1>) -> !firrtl.uint<3>
  %_v_7_T_1 = firrtl.node %88 : !firrtl.uint<3>
  %89 = firrtl.or %_v_7_T_1, %v_6 : (!firrtl.uint<3>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_v_7_T_2 = firrtl.node %89 : !firrtl.uint<4>
  firrtl.strictconnect %v_7, %_v_7_T_2 : !firrtl.uint<4>
  %90 = firrtl.bits %io_largeEncIn_4 8 to 8 : (!firrtl.uint<16>) -> !firrtl.uint<1>
  %_v_8_T = firrtl.node %90 : !firrtl.uint<1>
  %91 = firrtl.mux(%_v_8_T, %c8_ui4, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<1>) -> !firrtl.uint<4>
  %_v_8_T_1 = firrtl.node %91 : !firrtl.uint<4>
  %92 = firrtl.or %_v_8_T_1, %v_7 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_v_8_T_2 = firrtl.node %92 : !firrtl.uint<4>
  firrtl.strictconnect %v_8, %_v_8_T_2 : !firrtl.uint<4>
  %93 = firrtl.bits %io_largeEncIn_4 9 to 9 : (!firrtl.uint<16>) -> !firrtl.uint<1>
  %_v_9_T = firrtl.node %93 : !firrtl.uint<1>
  %c9_ui4 = firrtl.constant 9 : !firrtl.uint<4>
  %94 = firrtl.mux(%_v_9_T, %c9_ui4, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<1>) -> !firrtl.uint<4>
  %_v_9_T_1 = firrtl.node %94 : !firrtl.uint<4>
  %95 = firrtl.or %_v_9_T_1, %v_8 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_v_9_T_2 = firrtl.node %95 : !firrtl.uint<4>
  firrtl.strictconnect %v_9, %_v_9_T_2 : !firrtl.uint<4>
  %96 = firrtl.bits %io_largeEncIn_4 10 to 10 : (!firrtl.uint<16>) -> !firrtl.uint<1>
  %_v_10_T = firrtl.node %96 : !firrtl.uint<1>
  %c10_ui4 = firrtl.constant 10 : !firrtl.uint<4>
  %97 = firrtl.mux(%_v_10_T, %c10_ui4, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<1>) -> !firrtl.uint<4>
  %_v_10_T_1 = firrtl.node %97 : !firrtl.uint<4>
  %98 = firrtl.or %_v_10_T_1, %v_9 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_v_10_T_2 = firrtl.node %98 : !firrtl.uint<4>
  firrtl.strictconnect %v_10, %_v_10_T_2 : !firrtl.uint<4>
  %99 = firrtl.bits %io_largeEncIn_4 11 to 11 : (!firrtl.uint<16>) -> !firrtl.uint<1>
  %_v_11_T = firrtl.node %99 : !firrtl.uint<1>
  %c11_ui4 = firrtl.constant 11 : !firrtl.uint<4>
  %100 = firrtl.mux(%_v_11_T, %c11_ui4, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<1>) -> !firrtl.uint<4>
  %_v_11_T_1 = firrtl.node %100 : !firrtl.uint<4>
  %101 = firrtl.or %_v_11_T_1, %v_10 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_v_11_T_2 = firrtl.node %101 : !firrtl.uint<4>
  firrtl.strictconnect %v_11, %_v_11_T_2 : !firrtl.uint<4>
  %102 = firrtl.bits %io_largeEncIn_4 12 to 12 : (!firrtl.uint<16>) -> !firrtl.uint<1>
  %_v_12_T = firrtl.node %102 : !firrtl.uint<1>
  %c12_ui4 = firrtl.constant 12 : !firrtl.uint<4>
  %103 = firrtl.mux(%_v_12_T, %c12_ui4, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<1>) -> !firrtl.uint<4>
  %_v_12_T_1 = firrtl.node %103 : !firrtl.uint<4>
  %104 = firrtl.or %_v_12_T_1, %v_11 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_v_12_T_2 = firrtl.node %104 : !firrtl.uint<4>
  firrtl.strictconnect %v_12, %_v_12_T_2 : !firrtl.uint<4>
  %105 = firrtl.bits %io_largeEncIn_4 13 to 13 : (!firrtl.uint<16>) -> !firrtl.uint<1>
  %_v_13_T = firrtl.node %105 : !firrtl.uint<1>
  %c13_ui4 = firrtl.constant 13 : !firrtl.uint<4>
  %106 = firrtl.mux(%_v_13_T, %c13_ui4, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<1>) -> !firrtl.uint<4>
  %_v_13_T_1 = firrtl.node %106 : !firrtl.uint<4>
  %107 = firrtl.or %_v_13_T_1, %v_12 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_v_13_T_2 = firrtl.node %107 : !firrtl.uint<4>
  firrtl.strictconnect %v_13, %_v_13_T_2 : !firrtl.uint<4>
  %108 = firrtl.bits %io_largeEncIn_4 14 to 14 : (!firrtl.uint<16>) -> !firrtl.uint<1>
  %_v_14_T = firrtl.node %108 : !firrtl.uint<1>
  %c14_ui4 = firrtl.constant 14 : !firrtl.uint<4>
  %109 = firrtl.mux(%_v_14_T, %c14_ui4, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<1>) -> !firrtl.uint<4>
  %_v_14_T_1 = firrtl.node %109 : !firrtl.uint<4>
  %110 = firrtl.or %_v_14_T_1, %v_13 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_v_14_T_2 = firrtl.node %110 : !firrtl.uint<4>
  firrtl.strictconnect %v_14, %_v_14_T_2 : !firrtl.uint<4>
  %111 = firrtl.bits %io_largeEncIn_4 15 to 15 : (!firrtl.uint<16>) -> !firrtl.uint<1>
  %_v_15_T = firrtl.node %111 : !firrtl.uint<1>
  %c15_ui4 = firrtl.constant 15 : !firrtl.uint<4>
  %112 = firrtl.mux(%_v_15_T, %c15_ui4, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<1>) -> !firrtl.uint<4>
  %_v_15_T_1 = firrtl.node %112 : !firrtl.uint<4>
  %113 = firrtl.or %_v_15_T_1, %v_14 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %_v_15_T_2 = firrtl.node %113 : !firrtl.uint<4>
  firrtl.strictconnect %v_15, %_v_15_T_2 : !firrtl.uint<4>
  firrtl.strictconnect %io_largeEncOut_5, %v_15 : !firrtl.uint<4>
}

