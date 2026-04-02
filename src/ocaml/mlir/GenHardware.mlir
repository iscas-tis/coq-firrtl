// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @GenHardware(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, out %io_data_0: !firrtl.uint<8>, out %io_data_1: !firrtl.uint<8>, out %io_data_2: !firrtl.uint<8>, out %io_data_3: !firrtl.uint<8>, out %io_data_4: !firrtl.uint<8>, out %io_data_5: !firrtl.uint<8>, out %io_data_6: !firrtl.uint<8>, out %io_data_7: !firrtl.uint<8>, out %io_data_8: !firrtl.uint<8>, out %io_data_9: !firrtl.uint<8>, out %io_data_10: !firrtl.uint<8>, out %io_data_11: !firrtl.uint<8>, out %io_len: !firrtl.uint<8>, in %io_squareIn: !firrtl.uint<8>, out %io_squareOut: !firrtl.uint<8>) attributes {convention = #firrtl<convention scalarized>} {
  %io_data_0_0 = firrtl.wire {name = "io_data_0"} : !firrtl.uint<8>
  %io_data_1_1 = firrtl.wire {name = "io_data_1"} : !firrtl.uint<8>
  %io_data_2_2 = firrtl.wire {name = "io_data_2"} : !firrtl.uint<8>
  %io_data_3_3 = firrtl.wire {name = "io_data_3"} : !firrtl.uint<8>
  %io_data_4_4 = firrtl.wire {name = "io_data_4"} : !firrtl.uint<8>
  %io_data_5_5 = firrtl.wire {name = "io_data_5"} : !firrtl.uint<8>
  %io_data_6_6 = firrtl.wire {name = "io_data_6"} : !firrtl.uint<8>
  %io_data_7_7 = firrtl.wire {name = "io_data_7"} : !firrtl.uint<8>
  %io_data_8_8 = firrtl.wire {name = "io_data_8"} : !firrtl.uint<8>
  %io_data_9_9 = firrtl.wire {name = "io_data_9"} : !firrtl.uint<8>
  %io_data_10_10 = firrtl.wire {name = "io_data_10"} : !firrtl.uint<8>
  %io_data_11_11 = firrtl.wire {name = "io_data_11"} : !firrtl.uint<8>
  %io_len_12 = firrtl.wire {name = "io_len"} : !firrtl.uint<8>
  %io_squareIn_13 = firrtl.wire {name = "io_squareIn"} : !firrtl.uint<8>
  %io_squareOut_14 = firrtl.wire {name = "io_squareOut"} : !firrtl.uint<8>
  firrtl.strictconnect %io_data_0, %io_data_0_0 : !firrtl.uint<8>
  firrtl.strictconnect %io_data_1, %io_data_1_1 : !firrtl.uint<8>
  firrtl.strictconnect %io_data_2, %io_data_2_2 : !firrtl.uint<8>
  firrtl.strictconnect %io_data_3, %io_data_3_3 : !firrtl.uint<8>
  firrtl.strictconnect %io_data_4, %io_data_4_4 : !firrtl.uint<8>
  firrtl.strictconnect %io_data_5, %io_data_5_5 : !firrtl.uint<8>
  firrtl.strictconnect %io_data_6, %io_data_6_6 : !firrtl.uint<8>
  firrtl.strictconnect %io_data_7, %io_data_7_7 : !firrtl.uint<8>
  firrtl.strictconnect %io_data_8, %io_data_8_8 : !firrtl.uint<8>
  firrtl.strictconnect %io_data_9, %io_data_9_9 : !firrtl.uint<8>
  firrtl.strictconnect %io_data_10, %io_data_10_10 : !firrtl.uint<8>
  firrtl.strictconnect %io_data_11, %io_data_11_11 : !firrtl.uint<8>
  firrtl.strictconnect %io_len, %io_len_12 : !firrtl.uint<8>
  firrtl.strictconnect %io_squareIn_13, %io_squareIn : !firrtl.uint<8>
  firrtl.strictconnect %io_squareOut, %io_squareOut_14 : !firrtl.uint<8>
  %text_0 = firrtl.wire : !firrtl.uint<7>
  %text_1 = firrtl.wire : !firrtl.uint<7>
  %text_2 = firrtl.wire : !firrtl.uint<7>
  %text_3 = firrtl.wire : !firrtl.uint<7>
  %text_4 = firrtl.wire : !firrtl.uint<7>
  %text_5 = firrtl.wire : !firrtl.uint<7>
  %text_6 = firrtl.wire : !firrtl.uint<7>
  %text_7 = firrtl.wire : !firrtl.uint<7>
  %text_8 = firrtl.wire : !firrtl.uint<7>
  %text_9 = firrtl.wire : !firrtl.uint<7>
  %text_10 = firrtl.wire : !firrtl.uint<7>
  %text_11 = firrtl.wire : !firrtl.uint<7>
  %c72_ui7 = firrtl.constant 72 : !firrtl.uint<7>
  firrtl.strictconnect %text_0, %c72_ui7 : !firrtl.uint<7>
  %c101_ui7 = firrtl.constant 101 : !firrtl.uint<7>
  firrtl.strictconnect %text_1, %c101_ui7 : !firrtl.uint<7>
  %c108_ui7 = firrtl.constant 108 : !firrtl.uint<7>
  firrtl.strictconnect %text_2, %c108_ui7 : !firrtl.uint<7>
  firrtl.strictconnect %text_3, %c108_ui7 : !firrtl.uint<7>
  %c111_ui7 = firrtl.constant 111 : !firrtl.uint<7>
  firrtl.strictconnect %text_4, %c111_ui7 : !firrtl.uint<7>
  %c32_ui6 = firrtl.constant 32 : !firrtl.uint<6>
  %0 = firrtl.pad %c32_ui6, 7 : (!firrtl.uint<6>) -> !firrtl.uint<7>
  firrtl.strictconnect %text_5, %0 : !firrtl.uint<7>
  %c87_ui7 = firrtl.constant 87 : !firrtl.uint<7>
  firrtl.strictconnect %text_6, %c87_ui7 : !firrtl.uint<7>
  firrtl.strictconnect %text_7, %c111_ui7 : !firrtl.uint<7>
  %c114_ui7 = firrtl.constant 114 : !firrtl.uint<7>
  firrtl.strictconnect %text_8, %c114_ui7 : !firrtl.uint<7>
  firrtl.strictconnect %text_9, %c108_ui7 : !firrtl.uint<7>
  %c100_ui7 = firrtl.constant 100 : !firrtl.uint<7>
  firrtl.strictconnect %text_10, %c100_ui7 : !firrtl.uint<7>
  %c33_ui6 = firrtl.constant 33 : !firrtl.uint<6>
  %1 = firrtl.pad %c33_ui6, 7 : (!firrtl.uint<6>) -> !firrtl.uint<7>
  firrtl.strictconnect %text_11, %1 : !firrtl.uint<7>
  %squareROM_0 = firrtl.wire : !firrtl.uint<5>
  %squareROM_1 = firrtl.wire : !firrtl.uint<5>
  %squareROM_2 = firrtl.wire : !firrtl.uint<5>
  %squareROM_3 = firrtl.wire : !firrtl.uint<5>
  %squareROM_4 = firrtl.wire : !firrtl.uint<5>
  %squareROM_5 = firrtl.wire : !firrtl.uint<5>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %2 = firrtl.pad %c0_ui1, 5 : (!firrtl.uint<1>) -> !firrtl.uint<5>
  firrtl.strictconnect %squareROM_0, %2 : !firrtl.uint<5>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %3 = firrtl.pad %c1_ui1, 5 : (!firrtl.uint<1>) -> !firrtl.uint<5>
  firrtl.strictconnect %squareROM_1, %3 : !firrtl.uint<5>
  %c4_ui3 = firrtl.constant 4 : !firrtl.uint<3>
  %4 = firrtl.pad %c4_ui3, 5 : (!firrtl.uint<3>) -> !firrtl.uint<5>
  firrtl.strictconnect %squareROM_2, %4 : !firrtl.uint<5>
  %c9_ui4 = firrtl.constant 9 : !firrtl.uint<4>
  %5 = firrtl.pad %c9_ui4, 5 : (!firrtl.uint<4>) -> !firrtl.uint<5>
  firrtl.strictconnect %squareROM_3, %5 : !firrtl.uint<5>
  %c16_ui5 = firrtl.constant 16 : !firrtl.uint<5>
  firrtl.strictconnect %squareROM_4, %c16_ui5 : !firrtl.uint<5>
  %c25_ui5 = firrtl.constant 25 : !firrtl.uint<5>
  firrtl.strictconnect %squareROM_5, %c25_ui5 : !firrtl.uint<5>
  %6 = firrtl.bits %io_squareIn_13 2 to 0 : (!firrtl.uint<8>) -> !firrtl.uint<3>
  %_square_T = firrtl.node %6 : !firrtl.uint<3>
  %7 = firrtl.pad %text_0, 8 : (!firrtl.uint<7>) -> !firrtl.uint<8>
  firrtl.strictconnect %io_data_0_0, %7 : !firrtl.uint<8>
  %8 = firrtl.pad %text_1, 8 : (!firrtl.uint<7>) -> !firrtl.uint<8>
  firrtl.strictconnect %io_data_1_1, %8 : !firrtl.uint<8>
  %9 = firrtl.pad %text_2, 8 : (!firrtl.uint<7>) -> !firrtl.uint<8>
  firrtl.strictconnect %io_data_2_2, %9 : !firrtl.uint<8>
  %10 = firrtl.pad %text_3, 8 : (!firrtl.uint<7>) -> !firrtl.uint<8>
  firrtl.strictconnect %io_data_3_3, %10 : !firrtl.uint<8>
  %11 = firrtl.pad %text_4, 8 : (!firrtl.uint<7>) -> !firrtl.uint<8>
  firrtl.strictconnect %io_data_4_4, %11 : !firrtl.uint<8>
  %12 = firrtl.pad %text_5, 8 : (!firrtl.uint<7>) -> !firrtl.uint<8>
  firrtl.strictconnect %io_data_5_5, %12 : !firrtl.uint<8>
  %13 = firrtl.pad %text_6, 8 : (!firrtl.uint<7>) -> !firrtl.uint<8>
  firrtl.strictconnect %io_data_6_6, %13 : !firrtl.uint<8>
  %14 = firrtl.pad %text_7, 8 : (!firrtl.uint<7>) -> !firrtl.uint<8>
  firrtl.strictconnect %io_data_7_7, %14 : !firrtl.uint<8>
  %15 = firrtl.pad %text_8, 8 : (!firrtl.uint<7>) -> !firrtl.uint<8>
  firrtl.strictconnect %io_data_8_8, %15 : !firrtl.uint<8>
  %16 = firrtl.pad %text_9, 8 : (!firrtl.uint<7>) -> !firrtl.uint<8>
  firrtl.strictconnect %io_data_9_9, %16 : !firrtl.uint<8>
  %17 = firrtl.pad %text_10, 8 : (!firrtl.uint<7>) -> !firrtl.uint<8>
  firrtl.strictconnect %io_data_10_10, %17 : !firrtl.uint<8>
  %18 = firrtl.pad %text_11, 8 : (!firrtl.uint<7>) -> !firrtl.uint<8>
  firrtl.strictconnect %io_data_11_11, %18 : !firrtl.uint<8>
  %c12_ui4 = firrtl.constant 12 : !firrtl.uint<4>
  %19 = firrtl.pad %c12_ui4, 8 : (!firrtl.uint<4>) -> !firrtl.uint<8>
  firrtl.strictconnect %io_len_12, %19 : !firrtl.uint<8>
  %20 = firrtl.multibit_mux %_square_T, %squareROM_5, %squareROM_4, %squareROM_3, %squareROM_2, %squareROM_1, %squareROM_0 : !firrtl.uint<3>, !firrtl.uint<5>
  %21 = firrtl.pad %20, 8 : (!firrtl.uint<5>) -> !firrtl.uint<8>
  firrtl.strictconnect %io_squareOut_14, %21 : !firrtl.uint<8>
}

