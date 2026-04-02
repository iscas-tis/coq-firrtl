// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @RegisterFile(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %io_rs1: !firrtl.uint<5>, in %io_rs2: !firrtl.uint<5>, in %io_rd: !firrtl.uint<5>, in %io_wrData: !firrtl.uint<32>, in %io_wrEna: !firrtl.uint<1>, out %io_rs1Val: !firrtl.uint<32>, out %io_rs2Val: !firrtl.uint<32>, out %io_dbgPort_0: !firrtl.uint<32>, out %io_dbgPort_1: !firrtl.uint<32>, out %io_dbgPort_2: !firrtl.uint<32>, out %io_dbgPort_3: !firrtl.uint<32>, out %io_dbgPort_4: !firrtl.uint<32>, out %io_dbgPort_5: !firrtl.uint<32>, out %io_dbgPort_6: !firrtl.uint<32>, out %io_dbgPort_7: !firrtl.uint<32>, out %io_dbgPort_8: !firrtl.uint<32>, out %io_dbgPort_9: !firrtl.uint<32>, out %io_dbgPort_10: !firrtl.uint<32>, out %io_dbgPort_11: !firrtl.uint<32>, out %io_dbgPort_12: !firrtl.uint<32>, out %io_dbgPort_13: !firrtl.uint<32>, out %io_dbgPort_14: !firrtl.uint<32>, out %io_dbgPort_15: !firrtl.uint<32>, out %io_dbgPort_16: !firrtl.uint<32>, out %io_dbgPort_17: !firrtl.uint<32>, out %io_dbgPort_18: !firrtl.uint<32>, out %io_dbgPort_19: !firrtl.uint<32>, out %io_dbgPort_20: !firrtl.uint<32>, out %io_dbgPort_21: !firrtl.uint<32>, out %io_dbgPort_22: !firrtl.uint<32>, out %io_dbgPort_23: !firrtl.uint<32>, out %io_dbgPort_24: !firrtl.uint<32>, out %io_dbgPort_25: !firrtl.uint<32>, out %io_dbgPort_26: !firrtl.uint<32>, out %io_dbgPort_27: !firrtl.uint<32>, out %io_dbgPort_28: !firrtl.uint<32>, out %io_dbgPort_29: !firrtl.uint<32>, out %io_dbgPort_30: !firrtl.uint<32>, out %io_dbgPort_31: !firrtl.uint<32>) attributes {convention = #firrtl<convention scalarized>} {
  %io_rs1_0 = firrtl.wire {name = "io_rs1"} : !firrtl.uint<5>
  %io_rs2_1 = firrtl.wire {name = "io_rs2"} : !firrtl.uint<5>
  %io_rd_2 = firrtl.wire {name = "io_rd"} : !firrtl.uint<5>
  %io_wrData_3 = firrtl.wire {name = "io_wrData"} : !firrtl.uint<32>
  %io_wrEna_4 = firrtl.wire {name = "io_wrEna"} : !firrtl.uint<1>
  %io_rs1Val_5 = firrtl.wire {name = "io_rs1Val"} : !firrtl.uint<32>
  %io_rs2Val_6 = firrtl.wire {name = "io_rs2Val"} : !firrtl.uint<32>
  %io_dbgPort_0_7 = firrtl.wire {name = "io_dbgPort_0"} : !firrtl.uint<32>
  %io_dbgPort_1_8 = firrtl.wire {name = "io_dbgPort_1"} : !firrtl.uint<32>
  %io_dbgPort_2_9 = firrtl.wire {name = "io_dbgPort_2"} : !firrtl.uint<32>
  %io_dbgPort_3_10 = firrtl.wire {name = "io_dbgPort_3"} : !firrtl.uint<32>
  %io_dbgPort_4_11 = firrtl.wire {name = "io_dbgPort_4"} : !firrtl.uint<32>
  %io_dbgPort_5_12 = firrtl.wire {name = "io_dbgPort_5"} : !firrtl.uint<32>
  %io_dbgPort_6_13 = firrtl.wire {name = "io_dbgPort_6"} : !firrtl.uint<32>
  %io_dbgPort_7_14 = firrtl.wire {name = "io_dbgPort_7"} : !firrtl.uint<32>
  %io_dbgPort_8_15 = firrtl.wire {name = "io_dbgPort_8"} : !firrtl.uint<32>
  %io_dbgPort_9_16 = firrtl.wire {name = "io_dbgPort_9"} : !firrtl.uint<32>
  %io_dbgPort_10_17 = firrtl.wire {name = "io_dbgPort_10"} : !firrtl.uint<32>
  %io_dbgPort_11_18 = firrtl.wire {name = "io_dbgPort_11"} : !firrtl.uint<32>
  %io_dbgPort_12_19 = firrtl.wire {name = "io_dbgPort_12"} : !firrtl.uint<32>
  %io_dbgPort_13_20 = firrtl.wire {name = "io_dbgPort_13"} : !firrtl.uint<32>
  %io_dbgPort_14_21 = firrtl.wire {name = "io_dbgPort_14"} : !firrtl.uint<32>
  %io_dbgPort_15_22 = firrtl.wire {name = "io_dbgPort_15"} : !firrtl.uint<32>
  %io_dbgPort_16_23 = firrtl.wire {name = "io_dbgPort_16"} : !firrtl.uint<32>
  %io_dbgPort_17_24 = firrtl.wire {name = "io_dbgPort_17"} : !firrtl.uint<32>
  %io_dbgPort_18_25 = firrtl.wire {name = "io_dbgPort_18"} : !firrtl.uint<32>
  %io_dbgPort_19_26 = firrtl.wire {name = "io_dbgPort_19"} : !firrtl.uint<32>
  %io_dbgPort_20_27 = firrtl.wire {name = "io_dbgPort_20"} : !firrtl.uint<32>
  %io_dbgPort_21_28 = firrtl.wire {name = "io_dbgPort_21"} : !firrtl.uint<32>
  %io_dbgPort_22_29 = firrtl.wire {name = "io_dbgPort_22"} : !firrtl.uint<32>
  %io_dbgPort_23_30 = firrtl.wire {name = "io_dbgPort_23"} : !firrtl.uint<32>
  %io_dbgPort_24_31 = firrtl.wire {name = "io_dbgPort_24"} : !firrtl.uint<32>
  %io_dbgPort_25_32 = firrtl.wire {name = "io_dbgPort_25"} : !firrtl.uint<32>
  %io_dbgPort_26_33 = firrtl.wire {name = "io_dbgPort_26"} : !firrtl.uint<32>
  %io_dbgPort_27_34 = firrtl.wire {name = "io_dbgPort_27"} : !firrtl.uint<32>
  %io_dbgPort_28_35 = firrtl.wire {name = "io_dbgPort_28"} : !firrtl.uint<32>
  %io_dbgPort_29_36 = firrtl.wire {name = "io_dbgPort_29"} : !firrtl.uint<32>
  %io_dbgPort_30_37 = firrtl.wire {name = "io_dbgPort_30"} : !firrtl.uint<32>
  %io_dbgPort_31_38 = firrtl.wire {name = "io_dbgPort_31"} : !firrtl.uint<32>
  firrtl.strictconnect %io_rs1_0, %io_rs1 : !firrtl.uint<5>
  firrtl.strictconnect %io_rs2_1, %io_rs2 : !firrtl.uint<5>
  firrtl.strictconnect %io_rd_2, %io_rd : !firrtl.uint<5>
  firrtl.strictconnect %io_wrData_3, %io_wrData : !firrtl.uint<32>
  firrtl.strictconnect %io_wrEna_4, %io_wrEna : !firrtl.uint<1>
  firrtl.strictconnect %io_rs1Val, %io_rs1Val_5 : !firrtl.uint<32>
  firrtl.strictconnect %io_rs2Val, %io_rs2Val_6 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_0, %io_dbgPort_0_7 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_1, %io_dbgPort_1_8 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_2, %io_dbgPort_2_9 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_3, %io_dbgPort_3_10 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_4, %io_dbgPort_4_11 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_5, %io_dbgPort_5_12 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_6, %io_dbgPort_6_13 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_7, %io_dbgPort_7_14 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_8, %io_dbgPort_8_15 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_9, %io_dbgPort_9_16 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_10, %io_dbgPort_10_17 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_11, %io_dbgPort_11_18 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_12, %io_dbgPort_12_19 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_13, %io_dbgPort_13_20 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_14, %io_dbgPort_14_21 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_15, %io_dbgPort_15_22 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_16, %io_dbgPort_16_23 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_17, %io_dbgPort_17_24 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_18, %io_dbgPort_18_25 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_19, %io_dbgPort_19_26 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_20, %io_dbgPort_20_27 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_21, %io_dbgPort_21_28 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_22, %io_dbgPort_22_29 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_23, %io_dbgPort_23_30 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_24, %io_dbgPort_24_31 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_25, %io_dbgPort_25_32 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_26, %io_dbgPort_26_33 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_27, %io_dbgPort_27_34 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_28, %io_dbgPort_28_35 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_29, %io_dbgPort_29_36 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_30, %io_dbgPort_30_37 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_31, %io_dbgPort_31_38 : !firrtl.uint<32>
  %_regfile_WIRE_0 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_1 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_2 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_3 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_4 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_5 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_6 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_7 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_8 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_9 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_10 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_11 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_12 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_13 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_14 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_15 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_16 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_17 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_18 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_19 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_20 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_21 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_22 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_23 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_24 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_25 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_26 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_27 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_28 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_29 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_30 = firrtl.wire : !firrtl.uint<32>
  %_regfile_WIRE_31 = firrtl.wire : !firrtl.uint<32>
  %c0_ui32 = firrtl.constant 0 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_0, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_1, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_2, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_3, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_4, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_5, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_6, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_7, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_8, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_9, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_10, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_11, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_12, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_13, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_14, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_15, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_16, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_17, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_18, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_19, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_20, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_21, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_22, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_23, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_24, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_25, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_26, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_27, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_28, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_29, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_30, %c0_ui32 : !firrtl.uint<32>
  firrtl.strictconnect %_regfile_WIRE_31, %c0_ui32 : !firrtl.uint<32>
  %regfile_0 = firrtl.regreset %clock, %reset, %_regfile_WIRE_0 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_1 = firrtl.regreset %clock, %reset, %_regfile_WIRE_1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_2 = firrtl.regreset %clock, %reset, %_regfile_WIRE_2 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_3 = firrtl.regreset %clock, %reset, %_regfile_WIRE_3 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_4 = firrtl.regreset %clock, %reset, %_regfile_WIRE_4 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_5 = firrtl.regreset %clock, %reset, %_regfile_WIRE_5 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_6 = firrtl.regreset %clock, %reset, %_regfile_WIRE_6 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_7 = firrtl.regreset %clock, %reset, %_regfile_WIRE_7 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_8 = firrtl.regreset %clock, %reset, %_regfile_WIRE_8 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_9 = firrtl.regreset %clock, %reset, %_regfile_WIRE_9 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_10 = firrtl.regreset %clock, %reset, %_regfile_WIRE_10 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_11 = firrtl.regreset %clock, %reset, %_regfile_WIRE_11 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_12 = firrtl.regreset %clock, %reset, %_regfile_WIRE_12 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_13 = firrtl.regreset %clock, %reset, %_regfile_WIRE_13 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_14 = firrtl.regreset %clock, %reset, %_regfile_WIRE_14 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_15 = firrtl.regreset %clock, %reset, %_regfile_WIRE_15 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_16 = firrtl.regreset %clock, %reset, %_regfile_WIRE_16 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_17 = firrtl.regreset %clock, %reset, %_regfile_WIRE_17 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_18 = firrtl.regreset %clock, %reset, %_regfile_WIRE_18 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_19 = firrtl.regreset %clock, %reset, %_regfile_WIRE_19 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_20 = firrtl.regreset %clock, %reset, %_regfile_WIRE_20 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_21 = firrtl.regreset %clock, %reset, %_regfile_WIRE_21 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_22 = firrtl.regreset %clock, %reset, %_regfile_WIRE_22 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_23 = firrtl.regreset %clock, %reset, %_regfile_WIRE_23 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_24 = firrtl.regreset %clock, %reset, %_regfile_WIRE_24 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_25 = firrtl.regreset %clock, %reset, %_regfile_WIRE_25 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_26 = firrtl.regreset %clock, %reset, %_regfile_WIRE_26 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_27 = firrtl.regreset %clock, %reset, %_regfile_WIRE_27 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_28 = firrtl.regreset %clock, %reset, %_regfile_WIRE_28 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_29 = firrtl.regreset %clock, %reset, %_regfile_WIRE_29 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_30 = firrtl.regreset %clock, %reset, %_regfile_WIRE_30 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %regfile_31 = firrtl.regreset %clock, %reset, %_regfile_WIRE_31 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>
  %0 = firrtl.multibit_mux %io_rs1_0, %regfile_31, %regfile_30, %regfile_29, %regfile_28, %regfile_27, %regfile_26, %regfile_25, %regfile_24, %regfile_23, %regfile_22, %regfile_21, %regfile_20, %regfile_19, %regfile_18, %regfile_17, %regfile_16, %regfile_15, %regfile_14, %regfile_13, %regfile_12, %regfile_11, %regfile_10, %regfile_9, %regfile_8, %regfile_7, %regfile_6, %regfile_5, %regfile_4, %regfile_3, %regfile_2, %regfile_1, %regfile_0 : !firrtl.uint<5>, !firrtl.uint<32>
  firrtl.strictconnect %io_rs1Val_5, %0 : !firrtl.uint<32>
  %1 = firrtl.multibit_mux %io_rs2_1, %regfile_31, %regfile_30, %regfile_29, %regfile_28, %regfile_27, %regfile_26, %regfile_25, %regfile_24, %regfile_23, %regfile_22, %regfile_21, %regfile_20, %regfile_19, %regfile_18, %regfile_17, %regfile_16, %regfile_15, %regfile_14, %regfile_13, %regfile_12, %regfile_11, %regfile_10, %regfile_9, %regfile_8, %regfile_7, %regfile_6, %regfile_5, %regfile_4, %regfile_3, %regfile_2, %regfile_1, %regfile_0 : !firrtl.uint<5>, !firrtl.uint<32>
  firrtl.strictconnect %io_rs2Val_6, %1 : !firrtl.uint<32>
  %c0_ui5 = firrtl.constant 0 : !firrtl.uint<5>
  %2 = firrtl.eq %io_rd_2, %c0_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %3 = firrtl.and %io_wrEna_4, %2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %4 = firrtl.mux(%2, %io_wrData_3, %regfile_0) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %5 = firrtl.mux(%io_wrEna_4, %4, %regfile_0) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_0, %5 : !firrtl.uint<32>, !firrtl.uint<32>
  %c1_ui5 = firrtl.constant 1 : !firrtl.uint<5>
  %6 = firrtl.eq %io_rd_2, %c1_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %7 = firrtl.and %io_wrEna_4, %6 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %8 = firrtl.mux(%6, %io_wrData_3, %regfile_1) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %9 = firrtl.mux(%io_wrEna_4, %8, %regfile_1) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_1, %9 : !firrtl.uint<32>, !firrtl.uint<32>
  %c2_ui5 = firrtl.constant 2 : !firrtl.uint<5>
  %10 = firrtl.eq %io_rd_2, %c2_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %11 = firrtl.and %io_wrEna_4, %10 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %12 = firrtl.mux(%10, %io_wrData_3, %regfile_2) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %13 = firrtl.mux(%io_wrEna_4, %12, %regfile_2) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_2, %13 : !firrtl.uint<32>, !firrtl.uint<32>
  %c3_ui5 = firrtl.constant 3 : !firrtl.uint<5>
  %14 = firrtl.eq %io_rd_2, %c3_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %15 = firrtl.and %io_wrEna_4, %14 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %16 = firrtl.mux(%14, %io_wrData_3, %regfile_3) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %17 = firrtl.mux(%io_wrEna_4, %16, %regfile_3) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_3, %17 : !firrtl.uint<32>, !firrtl.uint<32>
  %c4_ui5 = firrtl.constant 4 : !firrtl.uint<5>
  %18 = firrtl.eq %io_rd_2, %c4_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %19 = firrtl.and %io_wrEna_4, %18 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %20 = firrtl.mux(%18, %io_wrData_3, %regfile_4) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %21 = firrtl.mux(%io_wrEna_4, %20, %regfile_4) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_4, %21 : !firrtl.uint<32>, !firrtl.uint<32>
  %c5_ui5 = firrtl.constant 5 : !firrtl.uint<5>
  %22 = firrtl.eq %io_rd_2, %c5_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %23 = firrtl.and %io_wrEna_4, %22 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %24 = firrtl.mux(%22, %io_wrData_3, %regfile_5) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %25 = firrtl.mux(%io_wrEna_4, %24, %regfile_5) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_5, %25 : !firrtl.uint<32>, !firrtl.uint<32>
  %c6_ui5 = firrtl.constant 6 : !firrtl.uint<5>
  %26 = firrtl.eq %io_rd_2, %c6_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %27 = firrtl.and %io_wrEna_4, %26 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %28 = firrtl.mux(%26, %io_wrData_3, %regfile_6) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %29 = firrtl.mux(%io_wrEna_4, %28, %regfile_6) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_6, %29 : !firrtl.uint<32>, !firrtl.uint<32>
  %c7_ui5 = firrtl.constant 7 : !firrtl.uint<5>
  %30 = firrtl.eq %io_rd_2, %c7_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %31 = firrtl.and %io_wrEna_4, %30 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %32 = firrtl.mux(%30, %io_wrData_3, %regfile_7) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %33 = firrtl.mux(%io_wrEna_4, %32, %regfile_7) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_7, %33 : !firrtl.uint<32>, !firrtl.uint<32>
  %c8_ui5 = firrtl.constant 8 : !firrtl.uint<5>
  %34 = firrtl.eq %io_rd_2, %c8_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %35 = firrtl.and %io_wrEna_4, %34 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %36 = firrtl.mux(%34, %io_wrData_3, %regfile_8) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %37 = firrtl.mux(%io_wrEna_4, %36, %regfile_8) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_8, %37 : !firrtl.uint<32>, !firrtl.uint<32>
  %c9_ui5 = firrtl.constant 9 : !firrtl.uint<5>
  %38 = firrtl.eq %io_rd_2, %c9_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %39 = firrtl.and %io_wrEna_4, %38 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %40 = firrtl.mux(%38, %io_wrData_3, %regfile_9) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %41 = firrtl.mux(%io_wrEna_4, %40, %regfile_9) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_9, %41 : !firrtl.uint<32>, !firrtl.uint<32>
  %c10_ui5 = firrtl.constant 10 : !firrtl.uint<5>
  %42 = firrtl.eq %io_rd_2, %c10_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %43 = firrtl.and %io_wrEna_4, %42 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %44 = firrtl.mux(%42, %io_wrData_3, %regfile_10) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %45 = firrtl.mux(%io_wrEna_4, %44, %regfile_10) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_10, %45 : !firrtl.uint<32>, !firrtl.uint<32>
  %c11_ui5 = firrtl.constant 11 : !firrtl.uint<5>
  %46 = firrtl.eq %io_rd_2, %c11_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %47 = firrtl.and %io_wrEna_4, %46 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %48 = firrtl.mux(%46, %io_wrData_3, %regfile_11) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %49 = firrtl.mux(%io_wrEna_4, %48, %regfile_11) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_11, %49 : !firrtl.uint<32>, !firrtl.uint<32>
  %c12_ui5 = firrtl.constant 12 : !firrtl.uint<5>
  %50 = firrtl.eq %io_rd_2, %c12_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %51 = firrtl.and %io_wrEna_4, %50 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %52 = firrtl.mux(%50, %io_wrData_3, %regfile_12) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %53 = firrtl.mux(%io_wrEna_4, %52, %regfile_12) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_12, %53 : !firrtl.uint<32>, !firrtl.uint<32>
  %c13_ui5 = firrtl.constant 13 : !firrtl.uint<5>
  %54 = firrtl.eq %io_rd_2, %c13_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %55 = firrtl.and %io_wrEna_4, %54 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %56 = firrtl.mux(%54, %io_wrData_3, %regfile_13) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %57 = firrtl.mux(%io_wrEna_4, %56, %regfile_13) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_13, %57 : !firrtl.uint<32>, !firrtl.uint<32>
  %c14_ui5 = firrtl.constant 14 : !firrtl.uint<5>
  %58 = firrtl.eq %io_rd_2, %c14_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %59 = firrtl.and %io_wrEna_4, %58 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %60 = firrtl.mux(%58, %io_wrData_3, %regfile_14) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %61 = firrtl.mux(%io_wrEna_4, %60, %regfile_14) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_14, %61 : !firrtl.uint<32>, !firrtl.uint<32>
  %c15_ui5 = firrtl.constant 15 : !firrtl.uint<5>
  %62 = firrtl.eq %io_rd_2, %c15_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %63 = firrtl.and %io_wrEna_4, %62 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %64 = firrtl.mux(%62, %io_wrData_3, %regfile_15) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %65 = firrtl.mux(%io_wrEna_4, %64, %regfile_15) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_15, %65 : !firrtl.uint<32>, !firrtl.uint<32>
  %c16_ui5 = firrtl.constant 16 : !firrtl.uint<5>
  %66 = firrtl.eq %io_rd_2, %c16_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %67 = firrtl.and %io_wrEna_4, %66 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %68 = firrtl.mux(%66, %io_wrData_3, %regfile_16) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %69 = firrtl.mux(%io_wrEna_4, %68, %regfile_16) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_16, %69 : !firrtl.uint<32>, !firrtl.uint<32>
  %c17_ui5 = firrtl.constant 17 : !firrtl.uint<5>
  %70 = firrtl.eq %io_rd_2, %c17_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %71 = firrtl.and %io_wrEna_4, %70 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %72 = firrtl.mux(%70, %io_wrData_3, %regfile_17) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %73 = firrtl.mux(%io_wrEna_4, %72, %regfile_17) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_17, %73 : !firrtl.uint<32>, !firrtl.uint<32>
  %c18_ui5 = firrtl.constant 18 : !firrtl.uint<5>
  %74 = firrtl.eq %io_rd_2, %c18_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %75 = firrtl.and %io_wrEna_4, %74 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %76 = firrtl.mux(%74, %io_wrData_3, %regfile_18) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %77 = firrtl.mux(%io_wrEna_4, %76, %regfile_18) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_18, %77 : !firrtl.uint<32>, !firrtl.uint<32>
  %c19_ui5 = firrtl.constant 19 : !firrtl.uint<5>
  %78 = firrtl.eq %io_rd_2, %c19_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %79 = firrtl.and %io_wrEna_4, %78 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %80 = firrtl.mux(%78, %io_wrData_3, %regfile_19) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %81 = firrtl.mux(%io_wrEna_4, %80, %regfile_19) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_19, %81 : !firrtl.uint<32>, !firrtl.uint<32>
  %c20_ui5 = firrtl.constant 20 : !firrtl.uint<5>
  %82 = firrtl.eq %io_rd_2, %c20_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %83 = firrtl.and %io_wrEna_4, %82 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %84 = firrtl.mux(%82, %io_wrData_3, %regfile_20) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %85 = firrtl.mux(%io_wrEna_4, %84, %regfile_20) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_20, %85 : !firrtl.uint<32>, !firrtl.uint<32>
  %c21_ui5 = firrtl.constant 21 : !firrtl.uint<5>
  %86 = firrtl.eq %io_rd_2, %c21_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %87 = firrtl.and %io_wrEna_4, %86 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %88 = firrtl.mux(%86, %io_wrData_3, %regfile_21) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %89 = firrtl.mux(%io_wrEna_4, %88, %regfile_21) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_21, %89 : !firrtl.uint<32>, !firrtl.uint<32>
  %c22_ui5 = firrtl.constant 22 : !firrtl.uint<5>
  %90 = firrtl.eq %io_rd_2, %c22_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %91 = firrtl.and %io_wrEna_4, %90 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %92 = firrtl.mux(%90, %io_wrData_3, %regfile_22) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %93 = firrtl.mux(%io_wrEna_4, %92, %regfile_22) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_22, %93 : !firrtl.uint<32>, !firrtl.uint<32>
  %c23_ui5 = firrtl.constant 23 : !firrtl.uint<5>
  %94 = firrtl.eq %io_rd_2, %c23_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %95 = firrtl.and %io_wrEna_4, %94 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %96 = firrtl.mux(%94, %io_wrData_3, %regfile_23) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %97 = firrtl.mux(%io_wrEna_4, %96, %regfile_23) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_23, %97 : !firrtl.uint<32>, !firrtl.uint<32>
  %c24_ui5 = firrtl.constant 24 : !firrtl.uint<5>
  %98 = firrtl.eq %io_rd_2, %c24_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %99 = firrtl.and %io_wrEna_4, %98 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %100 = firrtl.mux(%98, %io_wrData_3, %regfile_24) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %101 = firrtl.mux(%io_wrEna_4, %100, %regfile_24) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_24, %101 : !firrtl.uint<32>, !firrtl.uint<32>
  %c25_ui5 = firrtl.constant 25 : !firrtl.uint<5>
  %102 = firrtl.eq %io_rd_2, %c25_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %103 = firrtl.and %io_wrEna_4, %102 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %104 = firrtl.mux(%102, %io_wrData_3, %regfile_25) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %105 = firrtl.mux(%io_wrEna_4, %104, %regfile_25) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_25, %105 : !firrtl.uint<32>, !firrtl.uint<32>
  %c26_ui5 = firrtl.constant 26 : !firrtl.uint<5>
  %106 = firrtl.eq %io_rd_2, %c26_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %107 = firrtl.and %io_wrEna_4, %106 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %108 = firrtl.mux(%106, %io_wrData_3, %regfile_26) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %109 = firrtl.mux(%io_wrEna_4, %108, %regfile_26) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_26, %109 : !firrtl.uint<32>, !firrtl.uint<32>
  %c27_ui5 = firrtl.constant 27 : !firrtl.uint<5>
  %110 = firrtl.eq %io_rd_2, %c27_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %111 = firrtl.and %io_wrEna_4, %110 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %112 = firrtl.mux(%110, %io_wrData_3, %regfile_27) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %113 = firrtl.mux(%io_wrEna_4, %112, %regfile_27) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_27, %113 : !firrtl.uint<32>, !firrtl.uint<32>
  %c28_ui5 = firrtl.constant 28 : !firrtl.uint<5>
  %114 = firrtl.eq %io_rd_2, %c28_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %115 = firrtl.and %io_wrEna_4, %114 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %116 = firrtl.mux(%114, %io_wrData_3, %regfile_28) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %117 = firrtl.mux(%io_wrEna_4, %116, %regfile_28) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_28, %117 : !firrtl.uint<32>, !firrtl.uint<32>
  %c29_ui5 = firrtl.constant 29 : !firrtl.uint<5>
  %118 = firrtl.eq %io_rd_2, %c29_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %119 = firrtl.and %io_wrEna_4, %118 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %120 = firrtl.mux(%118, %io_wrData_3, %regfile_29) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %121 = firrtl.mux(%io_wrEna_4, %120, %regfile_29) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_29, %121 : !firrtl.uint<32>, !firrtl.uint<32>
  %c30_ui5 = firrtl.constant 30 : !firrtl.uint<5>
  %122 = firrtl.eq %io_rd_2, %c30_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %123 = firrtl.and %io_wrEna_4, %122 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %124 = firrtl.mux(%122, %io_wrData_3, %regfile_30) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %125 = firrtl.mux(%io_wrEna_4, %124, %regfile_30) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_30, %125 : !firrtl.uint<32>, !firrtl.uint<32>
  %c31_ui5 = firrtl.constant 31 : !firrtl.uint<5>
  %126 = firrtl.eq %io_rd_2, %c31_ui5 : (!firrtl.uint<5>, !firrtl.uint<5>) -> !firrtl.uint<1>
  %127 = firrtl.and %io_wrEna_4, %126 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %128 = firrtl.mux(%126, %io_wrData_3, %regfile_31) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  %129 = firrtl.mux(%io_wrEna_4, %128, %regfile_31) : (!firrtl.uint<1>, !firrtl.uint<32>, !firrtl.uint<32>) -> !firrtl.uint<32>
  firrtl.connect %regfile_31, %129 : !firrtl.uint<32>, !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_0_7, %regfile_0 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_1_8, %regfile_1 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_2_9, %regfile_2 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_3_10, %regfile_3 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_4_11, %regfile_4 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_5_12, %regfile_5 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_6_13, %regfile_6 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_7_14, %regfile_7 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_8_15, %regfile_8 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_9_16, %regfile_9 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_10_17, %regfile_10 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_11_18, %regfile_11 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_12_19, %regfile_12 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_13_20, %regfile_13 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_14_21, %regfile_14 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_15_22, %regfile_15 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_16_23, %regfile_16 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_17_24, %regfile_17 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_18_25, %regfile_18 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_19_26, %regfile_19 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_20_27, %regfile_20 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_21_28, %regfile_21 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_22_29, %regfile_22 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_23_30, %regfile_23 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_24_31, %regfile_24 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_25_32, %regfile_25 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_26_33, %regfile_26 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_27_34, %regfile_27 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_28_35, %regfile_28 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_29_36, %regfile_29 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_30_37, %regfile_30 : !firrtl.uint<32>
  firrtl.strictconnect %io_dbgPort_31_38, %regfile_31 : !firrtl.uint<32>
}

