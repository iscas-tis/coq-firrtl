// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @ArbiterTreeExperiments(in %clock1: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io_in_0_ready: !firrtl.uint<1>, in %io_in_0_valid: !firrtl.uint<1>, in %io_in_0_bits: !firrtl.uint<8>, out %io_in_1_ready: !firrtl.uint<1>, in %io_in_1_valid: !firrtl.uint<1>, in %io_in_1_bits: !firrtl.uint<8>, out %io_in_2_ready: !firrtl.uint<1>, in %io_in_2_valid: !firrtl.uint<1>, in %io_in_2_bits: !firrtl.uint<8>, out %io_in_3_ready: !firrtl.uint<1>, in %io_in_3_valid: !firrtl.uint<1>, in %io_in_3_bits: !firrtl.uint<8>, out %io_in_4_ready: !firrtl.uint<1>, in %io_in_4_valid: !firrtl.uint<1>, in %io_in_4_bits: !firrtl.uint<8>, out %io_in_5_ready: !firrtl.uint<1>, in %io_in_5_valid: !firrtl.uint<1>, in %io_in_5_bits: !firrtl.uint<8>, out %io_in_6_ready: !firrtl.uint<1>, in %io_in_6_valid: !firrtl.uint<1>, in %io_in_6_bits: !firrtl.uint<8>, in %io_out_ready: !firrtl.uint<1>, out %io_out_valid: !firrtl.uint<1>, out %io_out_bits: !firrtl.uint<8>) attributes {convention = #firrtl<convention scalarized>} {
  %io_in_0_ready_0 = firrtl.wire {name = "io_in_0_ready"} : !firrtl.uint<1>
  %io_in_0_valid_1 = firrtl.wire {name = "io_in_0_valid"} : !firrtl.uint<1>
  %io_in_0_bits_2 = firrtl.wire {name = "io_in_0_bits"} : !firrtl.uint<8>
  %io_in_1_ready_3 = firrtl.wire {name = "io_in_1_ready"} : !firrtl.uint<1>
  %io_in_1_valid_4 = firrtl.wire {name = "io_in_1_valid"} : !firrtl.uint<1>
  %io_in_1_bits_5 = firrtl.wire {name = "io_in_1_bits"} : !firrtl.uint<8>
  %io_in_2_ready_6 = firrtl.wire {name = "io_in_2_ready"} : !firrtl.uint<1>
  %io_in_2_valid_7 = firrtl.wire {name = "io_in_2_valid"} : !firrtl.uint<1>
  %io_in_2_bits_8 = firrtl.wire {name = "io_in_2_bits"} : !firrtl.uint<8>
  %io_in_3_ready_9 = firrtl.wire {name = "io_in_3_ready"} : !firrtl.uint<1>
  %io_in_3_valid_10 = firrtl.wire {name = "io_in_3_valid"} : !firrtl.uint<1>
  %io_in_3_bits_11 = firrtl.wire {name = "io_in_3_bits"} : !firrtl.uint<8>
  %io_in_4_ready_12 = firrtl.wire {name = "io_in_4_ready"} : !firrtl.uint<1>
  %io_in_4_valid_13 = firrtl.wire {name = "io_in_4_valid"} : !firrtl.uint<1>
  %io_in_4_bits_14 = firrtl.wire {name = "io_in_4_bits"} : !firrtl.uint<8>
  %io_in_5_ready_15 = firrtl.wire {name = "io_in_5_ready"} : !firrtl.uint<1>
  %io_in_5_valid_16 = firrtl.wire {name = "io_in_5_valid"} : !firrtl.uint<1>
  %io_in_5_bits_17 = firrtl.wire {name = "io_in_5_bits"} : !firrtl.uint<8>
  %io_in_6_ready_18 = firrtl.wire {name = "io_in_6_ready"} : !firrtl.uint<1>
  %io_in_6_valid_19 = firrtl.wire {name = "io_in_6_valid"} : !firrtl.uint<1>
  %io_in_6_bits_20 = firrtl.wire {name = "io_in_6_bits"} : !firrtl.uint<8>
  %io_out_ready_21 = firrtl.wire {name = "io_out_ready"} : !firrtl.uint<1>
  %io_out_valid_22 = firrtl.wire {name = "io_out_valid"} : !firrtl.uint<1>
  %io_out_bits_23 = firrtl.wire {name = "io_out_bits"} : !firrtl.uint<8>
  firrtl.strictconnect %io_in_0_ready, %io_in_0_ready_0 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_0_valid_1, %io_in_0_valid : !firrtl.uint<1>
  firrtl.strictconnect %io_in_0_bits_2, %io_in_0_bits : !firrtl.uint<8>
  firrtl.strictconnect %io_in_1_ready, %io_in_1_ready_3 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_1_valid_4, %io_in_1_valid : !firrtl.uint<1>
  firrtl.strictconnect %io_in_1_bits_5, %io_in_1_bits : !firrtl.uint<8>
  firrtl.strictconnect %io_in_2_ready, %io_in_2_ready_6 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_2_valid_7, %io_in_2_valid : !firrtl.uint<1>
  firrtl.strictconnect %io_in_2_bits_8, %io_in_2_bits : !firrtl.uint<8>
  firrtl.strictconnect %io_in_3_ready, %io_in_3_ready_9 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_3_valid_10, %io_in_3_valid : !firrtl.uint<1>
  firrtl.strictconnect %io_in_3_bits_11, %io_in_3_bits : !firrtl.uint<8>
  firrtl.strictconnect %io_in_4_ready, %io_in_4_ready_12 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_4_valid_13, %io_in_4_valid : !firrtl.uint<1>
  firrtl.strictconnect %io_in_4_bits_14, %io_in_4_bits : !firrtl.uint<8>
  firrtl.strictconnect %io_in_5_ready, %io_in_5_ready_15 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_5_valid_16, %io_in_5_valid : !firrtl.uint<1>
  firrtl.strictconnect %io_in_5_bits_17, %io_in_5_bits : !firrtl.uint<8>
  firrtl.strictconnect %io_in_6_ready, %io_in_6_ready_18 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_6_valid_19, %io_in_6_valid : !firrtl.uint<1>
  firrtl.strictconnect %io_in_6_bits_20, %io_in_6_bits : !firrtl.uint<8>
  firrtl.strictconnect %io_out_ready_21, %io_out_ready : !firrtl.uint<1>
  firrtl.strictconnect %io_out_valid, %io_out_valid_22 : !firrtl.uint<1>
  firrtl.strictconnect %io_out_bits, %io_out_bits_23 : !firrtl.uint<8>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %io_out_regData = firrtl.reg %clock1 : !firrtl.clock, !firrtl.uint<8>
  %io_out_regState = firrtl.regreset %clock1, %reset1, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<2>
  %io_out_out_ready = firrtl.wire : !firrtl.uint<1>
  %io_out_out_valid = firrtl.wire : !firrtl.uint<1>
  %io_out_out_bits = firrtl.wire : !firrtl.uint<8>
  %0 = firrtl.eq %io_out_regState, %c0_ui1 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_io_in_1_ready_T = firrtl.node %0 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_1_ready_3, %_io_out_io_in_1_ready_T : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %1 = firrtl.eq %io_out_regState, %c1_ui1 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_io_in_2_ready_T = firrtl.node %1 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_2_ready_6, %_io_out_io_in_2_ready_T : !firrtl.uint<1>
  %c2_ui2 = firrtl.constant 2 : !firrtl.uint<2>
  %2 = firrtl.eq %io_out_regState, %c2_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_out_valid_T = firrtl.node %2 : !firrtl.uint<1>
  %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
  %3 = firrtl.eq %io_out_regState, %c3_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_out_valid_T_1 = firrtl.node %3 : !firrtl.uint<1>
  %4 = firrtl.or %_io_out_out_valid_T, %_io_out_out_valid_T_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_out_valid_T_2 = firrtl.node %4 : !firrtl.uint<1>
  firrtl.strictconnect %io_out_out_valid, %_io_out_out_valid_T_2 : !firrtl.uint<1>
  %5 = firrtl.asUInt %c0_ui1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_T = firrtl.node %5 : !firrtl.uint<1>
  %6 = firrtl.asUInt %io_out_regState : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_1 = firrtl.node %6 : !firrtl.uint<2>
  %7 = firrtl.eq %_io_out_T, %_io_out_T_1 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_2 = firrtl.node %7 : !firrtl.uint<1>
  %8 = firrtl.and %_io_out_T_2, %io_in_1_valid_4 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %9 = firrtl.mux(%io_in_1_valid_4, %io_in_1_bits_5, %io_out_regData) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %10 = firrtl.not %io_in_1_valid_4 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %11 = firrtl.and %_io_out_T_2, %10 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %12 = firrtl.pad %c1_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %13 = firrtl.mux(%io_in_1_valid_4, %c2_ui2, %12) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %14 = firrtl.not %_io_out_T_2 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %15 = firrtl.asUInt %c1_ui1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_T_3 = firrtl.node %15 : !firrtl.uint<1>
  %_io_out_T_4 = firrtl.node %6 : !firrtl.uint<2>
  %16 = firrtl.eq %_io_out_T_3, %_io_out_T_4 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_5 = firrtl.node %16 : !firrtl.uint<1>
  %17 = firrtl.and %14, %_io_out_T_5 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %18 = firrtl.and %17, %io_in_2_valid_7 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %19 = firrtl.mux(%io_in_2_valid_7, %io_in_2_bits_8, %io_out_regData) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %20 = firrtl.mux(%_io_out_T_5, %19, %io_out_regData) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %21 = firrtl.mux(%_io_out_T_2, %9, %20) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  firrtl.connect %io_out_regData, %21 : !firrtl.uint<8>, !firrtl.uint<8>
  %22 = firrtl.not %io_in_2_valid_7 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %23 = firrtl.and %17, %22 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %24 = firrtl.pad %c0_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %25 = firrtl.mux(%io_in_2_valid_7, %c3_ui2, %24) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %26 = firrtl.not %_io_out_T_5 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %27 = firrtl.and %14, %26 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %28 = firrtl.asUInt %c2_ui2 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_6 = firrtl.node %28 : !firrtl.uint<2>
  %_io_out_T_7 = firrtl.node %6 : !firrtl.uint<2>
  %29 = firrtl.eq %_io_out_T_6, %_io_out_T_7 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_8 = firrtl.node %29 : !firrtl.uint<1>
  %30 = firrtl.and %27, %_io_out_T_8 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %31 = firrtl.and %30, %io_out_out_ready : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %32 = firrtl.pad %c1_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %33 = firrtl.mux(%io_out_out_ready, %32, %io_out_regState) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %34 = firrtl.not %_io_out_T_8 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %35 = firrtl.and %27, %34 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %36 = firrtl.asUInt %c3_ui2 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_9 = firrtl.node %36 : !firrtl.uint<2>
  %_io_out_T_10 = firrtl.node %6 : !firrtl.uint<2>
  %37 = firrtl.eq %_io_out_T_9, %_io_out_T_10 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_11 = firrtl.node %37 : !firrtl.uint<1>
  %38 = firrtl.and %35, %_io_out_T_11 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %39 = firrtl.and %38, %io_out_out_ready : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %40 = firrtl.pad %c0_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %41 = firrtl.mux(%io_out_out_ready, %40, %io_out_regState) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %42 = firrtl.mux(%_io_out_T_11, %41, %io_out_regState) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %43 = firrtl.mux(%_io_out_T_8, %33, %42) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %44 = firrtl.mux(%_io_out_T_5, %25, %43) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %45 = firrtl.mux(%_io_out_T_2, %13, %44) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  firrtl.connect %io_out_regState, %45 : !firrtl.uint<2>, !firrtl.uint<2>
  firrtl.strictconnect %io_out_out_bits, %io_out_regData : !firrtl.uint<8>
  %io_out_regData_1 = firrtl.reg %clock1 : !firrtl.clock, !firrtl.uint<8>
  %io_out_regState_1 = firrtl.regreset %clock1, %reset1, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<2>
  %io_out_out_1_ready = firrtl.wire : !firrtl.uint<1>
  %io_out_out_1_valid = firrtl.wire : !firrtl.uint<1>
  %io_out_out_1_bits = firrtl.wire : !firrtl.uint<8>
  %46 = firrtl.eq %io_out_regState_1, %c0_ui1 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_io_in_3_ready_T = firrtl.node %46 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_3_ready_9, %_io_out_io_in_3_ready_T : !firrtl.uint<1>
  %47 = firrtl.eq %io_out_regState_1, %c1_ui1 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_io_in_4_ready_T = firrtl.node %47 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_4_ready_12, %_io_out_io_in_4_ready_T : !firrtl.uint<1>
  %48 = firrtl.eq %io_out_regState_1, %c2_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_out_valid_T_3 = firrtl.node %48 : !firrtl.uint<1>
  %49 = firrtl.eq %io_out_regState_1, %c3_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_out_valid_T_4 = firrtl.node %49 : !firrtl.uint<1>
  %50 = firrtl.or %_io_out_out_valid_T_3, %_io_out_out_valid_T_4 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_out_valid_T_5 = firrtl.node %50 : !firrtl.uint<1>
  firrtl.strictconnect %io_out_out_1_valid, %_io_out_out_valid_T_5 : !firrtl.uint<1>
  %_io_out_T_12 = firrtl.node %5 : !firrtl.uint<1>
  %51 = firrtl.asUInt %io_out_regState_1 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_13 = firrtl.node %51 : !firrtl.uint<2>
  %52 = firrtl.eq %_io_out_T_12, %_io_out_T_13 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_14 = firrtl.node %52 : !firrtl.uint<1>
  %53 = firrtl.and %_io_out_T_14, %io_in_3_valid_10 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %54 = firrtl.mux(%io_in_3_valid_10, %io_in_3_bits_11, %io_out_regData_1) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %55 = firrtl.not %io_in_3_valid_10 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %56 = firrtl.and %_io_out_T_14, %55 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %57 = firrtl.pad %c1_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %58 = firrtl.mux(%io_in_3_valid_10, %c2_ui2, %57) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %59 = firrtl.not %_io_out_T_14 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %60 = firrtl.asUInt %c1_ui1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_T_15 = firrtl.node %60 : !firrtl.uint<1>
  %_io_out_T_16 = firrtl.node %51 : !firrtl.uint<2>
  %61 = firrtl.eq %_io_out_T_15, %_io_out_T_16 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_17 = firrtl.node %61 : !firrtl.uint<1>
  %62 = firrtl.and %59, %_io_out_T_17 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %63 = firrtl.and %62, %io_in_4_valid_13 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %64 = firrtl.mux(%io_in_4_valid_13, %io_in_4_bits_14, %io_out_regData_1) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %65 = firrtl.mux(%_io_out_T_17, %64, %io_out_regData_1) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %66 = firrtl.mux(%_io_out_T_14, %54, %65) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  firrtl.connect %io_out_regData_1, %66 : !firrtl.uint<8>, !firrtl.uint<8>
  %67 = firrtl.not %io_in_4_valid_13 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %68 = firrtl.and %62, %67 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %69 = firrtl.pad %c0_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %70 = firrtl.mux(%io_in_4_valid_13, %c3_ui2, %69) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %71 = firrtl.not %_io_out_T_17 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %72 = firrtl.and %59, %71 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %73 = firrtl.asUInt %c2_ui2 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_18 = firrtl.node %73 : !firrtl.uint<2>
  %_io_out_T_19 = firrtl.node %51 : !firrtl.uint<2>
  %74 = firrtl.eq %_io_out_T_18, %_io_out_T_19 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_20 = firrtl.node %74 : !firrtl.uint<1>
  %75 = firrtl.and %72, %_io_out_T_20 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %76 = firrtl.and %75, %io_out_out_1_ready : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %77 = firrtl.pad %c1_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %78 = firrtl.mux(%io_out_out_1_ready, %77, %io_out_regState_1) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %79 = firrtl.not %_io_out_T_20 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %80 = firrtl.and %72, %79 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %81 = firrtl.asUInt %c3_ui2 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_21 = firrtl.node %81 : !firrtl.uint<2>
  %_io_out_T_22 = firrtl.node %51 : !firrtl.uint<2>
  %82 = firrtl.eq %_io_out_T_21, %_io_out_T_22 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_23 = firrtl.node %82 : !firrtl.uint<1>
  %83 = firrtl.and %80, %_io_out_T_23 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %84 = firrtl.and %83, %io_out_out_1_ready : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %85 = firrtl.pad %c0_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %86 = firrtl.mux(%io_out_out_1_ready, %85, %io_out_regState_1) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %87 = firrtl.mux(%_io_out_T_23, %86, %io_out_regState_1) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %88 = firrtl.mux(%_io_out_T_20, %78, %87) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %89 = firrtl.mux(%_io_out_T_17, %70, %88) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %90 = firrtl.mux(%_io_out_T_14, %58, %89) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  firrtl.connect %io_out_regState_1, %90 : !firrtl.uint<2>, !firrtl.uint<2>
  firrtl.strictconnect %io_out_out_1_bits, %io_out_regData_1 : !firrtl.uint<8>
  %io_out_regData_2 = firrtl.reg %clock1 : !firrtl.clock, !firrtl.uint<8>
  %io_out_regState_2 = firrtl.regreset %clock1, %reset1, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<2>
  %io_out_out_2_ready = firrtl.wire : !firrtl.uint<1>
  %io_out_out_2_valid = firrtl.wire : !firrtl.uint<1>
  %io_out_out_2_bits = firrtl.wire : !firrtl.uint<8>
  %91 = firrtl.eq %io_out_regState_2, %c0_ui1 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_io_in_5_ready_T = firrtl.node %91 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_5_ready_15, %_io_out_io_in_5_ready_T : !firrtl.uint<1>
  %92 = firrtl.eq %io_out_regState_2, %c1_ui1 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_io_in_6_ready_T = firrtl.node %92 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_6_ready_18, %_io_out_io_in_6_ready_T : !firrtl.uint<1>
  %93 = firrtl.eq %io_out_regState_2, %c2_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_out_valid_T_6 = firrtl.node %93 : !firrtl.uint<1>
  %94 = firrtl.eq %io_out_regState_2, %c3_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_out_valid_T_7 = firrtl.node %94 : !firrtl.uint<1>
  %95 = firrtl.or %_io_out_out_valid_T_6, %_io_out_out_valid_T_7 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_out_valid_T_8 = firrtl.node %95 : !firrtl.uint<1>
  firrtl.strictconnect %io_out_out_2_valid, %_io_out_out_valid_T_8 : !firrtl.uint<1>
  %_io_out_T_24 = firrtl.node %5 : !firrtl.uint<1>
  %96 = firrtl.asUInt %io_out_regState_2 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_25 = firrtl.node %96 : !firrtl.uint<2>
  %97 = firrtl.eq %_io_out_T_24, %_io_out_T_25 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_26 = firrtl.node %97 : !firrtl.uint<1>
  %98 = firrtl.and %_io_out_T_26, %io_in_5_valid_16 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %99 = firrtl.mux(%io_in_5_valid_16, %io_in_5_bits_17, %io_out_regData_2) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %100 = firrtl.not %io_in_5_valid_16 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %101 = firrtl.and %_io_out_T_26, %100 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %102 = firrtl.pad %c1_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %103 = firrtl.mux(%io_in_5_valid_16, %c2_ui2, %102) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %104 = firrtl.not %_io_out_T_26 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %105 = firrtl.asUInt %c1_ui1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_T_27 = firrtl.node %105 : !firrtl.uint<1>
  %_io_out_T_28 = firrtl.node %96 : !firrtl.uint<2>
  %106 = firrtl.eq %_io_out_T_27, %_io_out_T_28 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_29 = firrtl.node %106 : !firrtl.uint<1>
  %107 = firrtl.and %104, %_io_out_T_29 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %108 = firrtl.and %107, %io_in_6_valid_19 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %109 = firrtl.mux(%io_in_6_valid_19, %io_in_6_bits_20, %io_out_regData_2) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %110 = firrtl.mux(%_io_out_T_29, %109, %io_out_regData_2) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %111 = firrtl.mux(%_io_out_T_26, %99, %110) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  firrtl.connect %io_out_regData_2, %111 : !firrtl.uint<8>, !firrtl.uint<8>
  %112 = firrtl.not %io_in_6_valid_19 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %113 = firrtl.and %107, %112 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %114 = firrtl.pad %c0_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %115 = firrtl.mux(%io_in_6_valid_19, %c3_ui2, %114) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %116 = firrtl.not %_io_out_T_29 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %117 = firrtl.and %104, %116 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %118 = firrtl.asUInt %c2_ui2 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_30 = firrtl.node %118 : !firrtl.uint<2>
  %_io_out_T_31 = firrtl.node %96 : !firrtl.uint<2>
  %119 = firrtl.eq %_io_out_T_30, %_io_out_T_31 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_32 = firrtl.node %119 : !firrtl.uint<1>
  %120 = firrtl.and %117, %_io_out_T_32 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %121 = firrtl.and %120, %io_out_out_2_ready : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %122 = firrtl.pad %c1_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %123 = firrtl.mux(%io_out_out_2_ready, %122, %io_out_regState_2) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %124 = firrtl.not %_io_out_T_32 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %125 = firrtl.and %117, %124 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %126 = firrtl.asUInt %c3_ui2 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_33 = firrtl.node %126 : !firrtl.uint<2>
  %_io_out_T_34 = firrtl.node %96 : !firrtl.uint<2>
  %127 = firrtl.eq %_io_out_T_33, %_io_out_T_34 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_35 = firrtl.node %127 : !firrtl.uint<1>
  %128 = firrtl.and %125, %_io_out_T_35 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %129 = firrtl.and %128, %io_out_out_2_ready : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %130 = firrtl.pad %c0_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %131 = firrtl.mux(%io_out_out_2_ready, %130, %io_out_regState_2) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %132 = firrtl.mux(%_io_out_T_35, %131, %io_out_regState_2) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %133 = firrtl.mux(%_io_out_T_32, %123, %132) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %134 = firrtl.mux(%_io_out_T_29, %115, %133) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %135 = firrtl.mux(%_io_out_T_26, %103, %134) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  firrtl.connect %io_out_regState_2, %135 : !firrtl.uint<2>, !firrtl.uint<2>
  firrtl.strictconnect %io_out_out_2_bits, %io_out_regData_2 : !firrtl.uint<8>
  %io_out_regData_3 = firrtl.reg %clock1 : !firrtl.clock, !firrtl.uint<8>
  %io_out_regState_3 = firrtl.regreset %clock1, %reset1, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<2>
  %io_out_out_3_ready = firrtl.wire : !firrtl.uint<1>
  %io_out_out_3_valid = firrtl.wire : !firrtl.uint<1>
  %io_out_out_3_bits = firrtl.wire : !firrtl.uint<8>
  %136 = firrtl.eq %io_out_regState_3, %c0_ui1 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_io_in_0_ready_T = firrtl.node %136 : !firrtl.uint<1>
  firrtl.strictconnect %io_in_0_ready_0, %_io_out_io_in_0_ready_T : !firrtl.uint<1>
  %137 = firrtl.eq %io_out_regState_3, %c1_ui1 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_out_ready_T = firrtl.node %137 : !firrtl.uint<1>
  firrtl.strictconnect %io_out_out_ready, %_io_out_out_ready_T : !firrtl.uint<1>
  %138 = firrtl.eq %io_out_regState_3, %c2_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_out_valid_T_9 = firrtl.node %138 : !firrtl.uint<1>
  %139 = firrtl.eq %io_out_regState_3, %c3_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_out_valid_T_10 = firrtl.node %139 : !firrtl.uint<1>
  %140 = firrtl.or %_io_out_out_valid_T_9, %_io_out_out_valid_T_10 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_out_valid_T_11 = firrtl.node %140 : !firrtl.uint<1>
  firrtl.strictconnect %io_out_out_3_valid, %_io_out_out_valid_T_11 : !firrtl.uint<1>
  %_io_out_T_36 = firrtl.node %5 : !firrtl.uint<1>
  %141 = firrtl.asUInt %io_out_regState_3 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_37 = firrtl.node %141 : !firrtl.uint<2>
  %142 = firrtl.eq %_io_out_T_36, %_io_out_T_37 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_38 = firrtl.node %142 : !firrtl.uint<1>
  %143 = firrtl.and %_io_out_T_38, %io_in_0_valid_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %144 = firrtl.mux(%io_in_0_valid_1, %io_in_0_bits_2, %io_out_regData_3) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %145 = firrtl.not %io_in_0_valid_1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %146 = firrtl.and %_io_out_T_38, %145 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %147 = firrtl.pad %c1_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %148 = firrtl.mux(%io_in_0_valid_1, %c2_ui2, %147) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %149 = firrtl.not %_io_out_T_38 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %150 = firrtl.asUInt %c1_ui1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_T_39 = firrtl.node %150 : !firrtl.uint<1>
  %_io_out_T_40 = firrtl.node %141 : !firrtl.uint<2>
  %151 = firrtl.eq %_io_out_T_39, %_io_out_T_40 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_41 = firrtl.node %151 : !firrtl.uint<1>
  %152 = firrtl.and %149, %_io_out_T_41 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %153 = firrtl.and %152, %io_out_out_valid : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %154 = firrtl.mux(%io_out_out_valid, %io_out_out_bits, %io_out_regData_3) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %155 = firrtl.mux(%_io_out_T_41, %154, %io_out_regData_3) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %156 = firrtl.mux(%_io_out_T_38, %144, %155) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  firrtl.connect %io_out_regData_3, %156 : !firrtl.uint<8>, !firrtl.uint<8>
  %157 = firrtl.not %io_out_out_valid : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %158 = firrtl.and %152, %157 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %159 = firrtl.pad %c0_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %160 = firrtl.mux(%io_out_out_valid, %c3_ui2, %159) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %161 = firrtl.not %_io_out_T_41 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %162 = firrtl.and %149, %161 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %163 = firrtl.asUInt %c2_ui2 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_42 = firrtl.node %163 : !firrtl.uint<2>
  %_io_out_T_43 = firrtl.node %141 : !firrtl.uint<2>
  %164 = firrtl.eq %_io_out_T_42, %_io_out_T_43 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_44 = firrtl.node %164 : !firrtl.uint<1>
  %165 = firrtl.and %162, %_io_out_T_44 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %166 = firrtl.and %165, %io_out_out_3_ready : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %167 = firrtl.pad %c1_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %168 = firrtl.mux(%io_out_out_3_ready, %167, %io_out_regState_3) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %169 = firrtl.not %_io_out_T_44 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %170 = firrtl.and %162, %169 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %171 = firrtl.asUInt %c3_ui2 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_45 = firrtl.node %171 : !firrtl.uint<2>
  %_io_out_T_46 = firrtl.node %141 : !firrtl.uint<2>
  %172 = firrtl.eq %_io_out_T_45, %_io_out_T_46 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_47 = firrtl.node %172 : !firrtl.uint<1>
  %173 = firrtl.and %170, %_io_out_T_47 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %174 = firrtl.and %173, %io_out_out_3_ready : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %175 = firrtl.pad %c0_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %176 = firrtl.mux(%io_out_out_3_ready, %175, %io_out_regState_3) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %177 = firrtl.mux(%_io_out_T_47, %176, %io_out_regState_3) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %178 = firrtl.mux(%_io_out_T_44, %168, %177) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %179 = firrtl.mux(%_io_out_T_41, %160, %178) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %180 = firrtl.mux(%_io_out_T_38, %148, %179) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  firrtl.connect %io_out_regState_3, %180 : !firrtl.uint<2>, !firrtl.uint<2>
  firrtl.strictconnect %io_out_out_3_bits, %io_out_regData_3 : !firrtl.uint<8>
  %io_out_regData_4 = firrtl.reg %clock1 : !firrtl.clock, !firrtl.uint<8>
  %io_out_regState_4 = firrtl.regreset %clock1, %reset1, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<2>
  %io_out_out_4_ready = firrtl.wire : !firrtl.uint<1>
  %io_out_out_4_valid = firrtl.wire : !firrtl.uint<1>
  %io_out_out_4_bits = firrtl.wire : !firrtl.uint<8>
  %181 = firrtl.eq %io_out_regState_4, %c0_ui1 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_out_ready_T_1 = firrtl.node %181 : !firrtl.uint<1>
  firrtl.strictconnect %io_out_out_1_ready, %_io_out_out_ready_T_1 : !firrtl.uint<1>
  %182 = firrtl.eq %io_out_regState_4, %c1_ui1 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_out_ready_T_2 = firrtl.node %182 : !firrtl.uint<1>
  firrtl.strictconnect %io_out_out_2_ready, %_io_out_out_ready_T_2 : !firrtl.uint<1>
  %183 = firrtl.eq %io_out_regState_4, %c2_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_out_valid_T_12 = firrtl.node %183 : !firrtl.uint<1>
  %184 = firrtl.eq %io_out_regState_4, %c3_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_out_valid_T_13 = firrtl.node %184 : !firrtl.uint<1>
  %185 = firrtl.or %_io_out_out_valid_T_12, %_io_out_out_valid_T_13 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_out_valid_T_14 = firrtl.node %185 : !firrtl.uint<1>
  firrtl.strictconnect %io_out_out_4_valid, %_io_out_out_valid_T_14 : !firrtl.uint<1>
  %_io_out_T_48 = firrtl.node %5 : !firrtl.uint<1>
  %186 = firrtl.asUInt %io_out_regState_4 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_49 = firrtl.node %186 : !firrtl.uint<2>
  %187 = firrtl.eq %_io_out_T_48, %_io_out_T_49 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_50 = firrtl.node %187 : !firrtl.uint<1>
  %188 = firrtl.and %_io_out_T_50, %io_out_out_1_valid : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %189 = firrtl.mux(%io_out_out_1_valid, %io_out_out_1_bits, %io_out_regData_4) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %190 = firrtl.not %io_out_out_1_valid : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %191 = firrtl.and %_io_out_T_50, %190 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %192 = firrtl.pad %c1_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %193 = firrtl.mux(%io_out_out_1_valid, %c2_ui2, %192) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %194 = firrtl.not %_io_out_T_50 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %195 = firrtl.asUInt %c1_ui1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_T_51 = firrtl.node %195 : !firrtl.uint<1>
  %_io_out_T_52 = firrtl.node %186 : !firrtl.uint<2>
  %196 = firrtl.eq %_io_out_T_51, %_io_out_T_52 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_53 = firrtl.node %196 : !firrtl.uint<1>
  %197 = firrtl.and %194, %_io_out_T_53 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %198 = firrtl.and %197, %io_out_out_2_valid : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %199 = firrtl.mux(%io_out_out_2_valid, %io_out_out_2_bits, %io_out_regData_4) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %200 = firrtl.mux(%_io_out_T_53, %199, %io_out_regData_4) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %201 = firrtl.mux(%_io_out_T_50, %189, %200) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  firrtl.connect %io_out_regData_4, %201 : !firrtl.uint<8>, !firrtl.uint<8>
  %202 = firrtl.not %io_out_out_2_valid : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %203 = firrtl.and %197, %202 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %204 = firrtl.pad %c0_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %205 = firrtl.mux(%io_out_out_2_valid, %c3_ui2, %204) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %206 = firrtl.not %_io_out_T_53 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %207 = firrtl.and %194, %206 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %208 = firrtl.asUInt %c2_ui2 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_54 = firrtl.node %208 : !firrtl.uint<2>
  %_io_out_T_55 = firrtl.node %186 : !firrtl.uint<2>
  %209 = firrtl.eq %_io_out_T_54, %_io_out_T_55 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_56 = firrtl.node %209 : !firrtl.uint<1>
  %210 = firrtl.and %207, %_io_out_T_56 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %211 = firrtl.and %210, %io_out_out_4_ready : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %212 = firrtl.pad %c1_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %213 = firrtl.mux(%io_out_out_4_ready, %212, %io_out_regState_4) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %214 = firrtl.not %_io_out_T_56 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %215 = firrtl.and %207, %214 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %216 = firrtl.asUInt %c3_ui2 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_57 = firrtl.node %216 : !firrtl.uint<2>
  %_io_out_T_58 = firrtl.node %186 : !firrtl.uint<2>
  %217 = firrtl.eq %_io_out_T_57, %_io_out_T_58 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_59 = firrtl.node %217 : !firrtl.uint<1>
  %218 = firrtl.and %215, %_io_out_T_59 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %219 = firrtl.and %218, %io_out_out_4_ready : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %220 = firrtl.pad %c0_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %221 = firrtl.mux(%io_out_out_4_ready, %220, %io_out_regState_4) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %222 = firrtl.mux(%_io_out_T_59, %221, %io_out_regState_4) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %223 = firrtl.mux(%_io_out_T_56, %213, %222) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %224 = firrtl.mux(%_io_out_T_53, %205, %223) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %225 = firrtl.mux(%_io_out_T_50, %193, %224) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  firrtl.connect %io_out_regState_4, %225 : !firrtl.uint<2>, !firrtl.uint<2>
  firrtl.strictconnect %io_out_out_4_bits, %io_out_regData_4 : !firrtl.uint<8>
  %io_out_regData_5 = firrtl.reg %clock1 : !firrtl.clock, !firrtl.uint<8>
  %io_out_regState_5 = firrtl.regreset %clock1, %reset1, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<2>
  %io_out_out_5_ready = firrtl.wire : !firrtl.uint<1>
  %io_out_out_5_valid = firrtl.wire : !firrtl.uint<1>
  %io_out_out_5_bits = firrtl.wire : !firrtl.uint<8>
  %226 = firrtl.eq %io_out_regState_5, %c0_ui1 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_out_ready_T_3 = firrtl.node %226 : !firrtl.uint<1>
  firrtl.strictconnect %io_out_out_3_ready, %_io_out_out_ready_T_3 : !firrtl.uint<1>
  %227 = firrtl.eq %io_out_regState_5, %c1_ui1 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_out_ready_T_4 = firrtl.node %227 : !firrtl.uint<1>
  firrtl.strictconnect %io_out_out_4_ready, %_io_out_out_ready_T_4 : !firrtl.uint<1>
  %228 = firrtl.eq %io_out_regState_5, %c2_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_out_valid_T_15 = firrtl.node %228 : !firrtl.uint<1>
  %229 = firrtl.eq %io_out_regState_5, %c3_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_out_valid_T_16 = firrtl.node %229 : !firrtl.uint<1>
  %230 = firrtl.or %_io_out_out_valid_T_15, %_io_out_out_valid_T_16 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_out_valid_T_17 = firrtl.node %230 : !firrtl.uint<1>
  firrtl.strictconnect %io_out_out_5_valid, %_io_out_out_valid_T_17 : !firrtl.uint<1>
  %_io_out_T_60 = firrtl.node %5 : !firrtl.uint<1>
  %231 = firrtl.asUInt %io_out_regState_5 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_61 = firrtl.node %231 : !firrtl.uint<2>
  %232 = firrtl.eq %_io_out_T_60, %_io_out_T_61 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_62 = firrtl.node %232 : !firrtl.uint<1>
  %233 = firrtl.and %_io_out_T_62, %io_out_out_3_valid : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %234 = firrtl.mux(%io_out_out_3_valid, %io_out_out_3_bits, %io_out_regData_5) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %235 = firrtl.not %io_out_out_3_valid : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %236 = firrtl.and %_io_out_T_62, %235 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %237 = firrtl.pad %c1_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %238 = firrtl.mux(%io_out_out_3_valid, %c2_ui2, %237) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %239 = firrtl.not %_io_out_T_62 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %240 = firrtl.asUInt %c1_ui1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_out_T_63 = firrtl.node %240 : !firrtl.uint<1>
  %_io_out_T_64 = firrtl.node %231 : !firrtl.uint<2>
  %241 = firrtl.eq %_io_out_T_63, %_io_out_T_64 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_65 = firrtl.node %241 : !firrtl.uint<1>
  %242 = firrtl.and %239, %_io_out_T_65 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %243 = firrtl.and %242, %io_out_out_4_valid : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %244 = firrtl.mux(%io_out_out_4_valid, %io_out_out_4_bits, %io_out_regData_5) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %245 = firrtl.mux(%_io_out_T_65, %244, %io_out_regData_5) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %246 = firrtl.mux(%_io_out_T_62, %234, %245) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  firrtl.connect %io_out_regData_5, %246 : !firrtl.uint<8>, !firrtl.uint<8>
  %247 = firrtl.not %io_out_out_4_valid : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %248 = firrtl.and %242, %247 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %249 = firrtl.pad %c0_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %250 = firrtl.mux(%io_out_out_4_valid, %c3_ui2, %249) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %251 = firrtl.not %_io_out_T_65 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %252 = firrtl.and %239, %251 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %253 = firrtl.asUInt %c2_ui2 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_66 = firrtl.node %253 : !firrtl.uint<2>
  %_io_out_T_67 = firrtl.node %231 : !firrtl.uint<2>
  %254 = firrtl.eq %_io_out_T_66, %_io_out_T_67 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_68 = firrtl.node %254 : !firrtl.uint<1>
  %255 = firrtl.and %252, %_io_out_T_68 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %256 = firrtl.and %255, %io_out_out_5_ready : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %257 = firrtl.pad %c1_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %258 = firrtl.mux(%io_out_out_5_ready, %257, %io_out_regState_5) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %259 = firrtl.not %_io_out_T_68 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %260 = firrtl.and %252, %259 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %261 = firrtl.asUInt %c3_ui2 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %_io_out_T_69 = firrtl.node %261 : !firrtl.uint<2>
  %_io_out_T_70 = firrtl.node %231 : !firrtl.uint<2>
  %262 = firrtl.eq %_io_out_T_69, %_io_out_T_70 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_out_T_71 = firrtl.node %262 : !firrtl.uint<1>
  %263 = firrtl.and %260, %_io_out_T_71 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %264 = firrtl.and %263, %io_out_out_5_ready : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %265 = firrtl.pad %c0_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %266 = firrtl.mux(%io_out_out_5_ready, %265, %io_out_regState_5) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %267 = firrtl.mux(%_io_out_T_71, %266, %io_out_regState_5) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %268 = firrtl.mux(%_io_out_T_68, %258, %267) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %269 = firrtl.mux(%_io_out_T_65, %250, %268) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %270 = firrtl.mux(%_io_out_T_62, %238, %269) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  firrtl.connect %io_out_regState_5, %270 : !firrtl.uint<2>, !firrtl.uint<2>
  firrtl.strictconnect %io_out_out_5_bits, %io_out_regData_5 : !firrtl.uint<8>
  firrtl.strictconnect %io_out_out_5_ready, %io_out_ready_21 : !firrtl.uint<1>
  firrtl.strictconnect %io_out_valid_22, %io_out_out_5_valid : !firrtl.uint<1>
  firrtl.strictconnect %io_out_bits_23, %io_out_out_5_bits : !firrtl.uint<8>
}

