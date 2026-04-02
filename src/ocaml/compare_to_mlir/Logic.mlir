// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @Logic(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %io_a: !firrtl.uint<1>, in %io_b: !firrtl.uint<1>, in %io_c: !firrtl.uint<1>, out %io_out: !firrtl.uint<1>, out %io_cat: !firrtl.uint<16>, out %io_ch: !firrtl.uint<8>, out %io_word: !firrtl.uint<16>, out %io_result: !firrtl.uint<4>) attributes {convention = #firrtl<convention scalarized>} {
  %io_a_0 = firrtl.wire {name = "io_a"} : !firrtl.uint<1>
  %io_b_1 = firrtl.wire {name = "io_b"} : !firrtl.uint<1>
  %io_c_2 = firrtl.wire {name = "io_c"} : !firrtl.uint<1>
  %io_out_3 = firrtl.wire {name = "io_out"} : !firrtl.uint<1>
  %io_cat_4 = firrtl.wire {name = "io_cat"} : !firrtl.uint<16>
  %io_ch_5 = firrtl.wire {name = "io_ch"} : !firrtl.uint<8>
  %io_word_6 = firrtl.wire {name = "io_word"} : !firrtl.uint<16>
  %io_result_7 = firrtl.wire {name = "io_result"} : !firrtl.uint<4>
  firrtl.strictconnect %io_a_0, %io_a : !firrtl.uint<1>
  firrtl.strictconnect %io_b_1, %io_b : !firrtl.uint<1>
  firrtl.strictconnect %io_c_2, %io_c : !firrtl.uint<1>
  firrtl.strictconnect %io_out, %io_out_3 : !firrtl.uint<1>
  firrtl.strictconnect %io_cat, %io_cat_4 : !firrtl.uint<16>
  firrtl.strictconnect %io_ch, %io_ch_5 : !firrtl.uint<8>
  firrtl.strictconnect %io_word, %io_word_6 : !firrtl.uint<16>
  firrtl.strictconnect %io_result, %io_result_7 : !firrtl.uint<4>
  %c65_ui7 = firrtl.constant 65 : !firrtl.uint<7>
  %0 = firrtl.pad %c65_ui7, 8 : (!firrtl.uint<7>) -> !firrtl.uint<8>
  firrtl.strictconnect %io_ch_5, %0 : !firrtl.uint<8>
  %1 = firrtl.and %io_a_0, %io_b_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_logic_T = firrtl.node %1 : !firrtl.uint<1>
  %2 = firrtl.or %_logic_T, %io_c_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %logic = firrtl.node %2 : !firrtl.uint<1>
  firrtl.strictconnect %io_out_3, %logic : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %3 = firrtl.and %c1_ui1, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %bop = firrtl.node %3 : !firrtl.uint<1>
  %and = firrtl.node %1 : !firrtl.uint<1>
  %4 = firrtl.or %io_a_0, %io_b_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %or = firrtl.node %4 : !firrtl.uint<1>
  %5 = firrtl.xor %io_a_0, %io_b_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %xor = firrtl.node %5 : !firrtl.uint<1>
  %6 = firrtl.not %io_a_0 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %not = firrtl.node %6 : !firrtl.uint<1>
  %7 = firrtl.add %io_a_0, %io_b_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %_add_T = firrtl.node %7 : !firrtl.uint<2>
  %8 = firrtl.tail %_add_T, 1 : (!firrtl.uint<2>) -> !firrtl.uint<1>
  %add = firrtl.node %8 : !firrtl.uint<1>
  %9 = firrtl.sub %io_a_0, %io_b_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %_sub_T = firrtl.node %9 : !firrtl.uint<2>
  %10 = firrtl.tail %_sub_T, 1 : (!firrtl.uint<2>) -> !firrtl.uint<1>
  %sub = firrtl.node %10 : !firrtl.uint<1>
  %11 = firrtl.sub %c0_ui1, %io_a_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %_neg_T = firrtl.node %11 : !firrtl.uint<2>
  %12 = firrtl.tail %_neg_T, 1 : (!firrtl.uint<2>) -> !firrtl.uint<1>
  %neg = firrtl.node %12 : !firrtl.uint<1>
  %13 = firrtl.mul %io_a_0, %io_b_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %mul = firrtl.node %13 : !firrtl.uint<2>
  %14 = firrtl.div %io_a_0, %io_b_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %div = firrtl.node %14 : !firrtl.uint<1>
  %15 = firrtl.rem %io_a_0, %io_b_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %mod = firrtl.node %15 : !firrtl.uint<1>
  %w = firrtl.wire : !firrtl.uint<1>
  %_w_T = firrtl.node %1 : !firrtl.uint<1>
  firrtl.connect %w, %_w_T : !firrtl.uint<1>, !firrtl.uint<1>
  %c255_ui8 = firrtl.constant 255 : !firrtl.uint<8>
  %c1_ui8 = firrtl.constant 1 : !firrtl.uint<8>
  %16 = firrtl.cat %c255_ui8, %c1_ui8 : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<16>
  %word = firrtl.node %16 : !firrtl.uint<16>
  firrtl.strictconnect %io_cat_4, %word : !firrtl.uint<16>
  %17 = firrtl.eq %io_b_1, %io_c_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %sel = firrtl.node %17 : !firrtl.uint<1>
  %18 = firrtl.mux(%sel, %io_a_0, %io_b_1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %result = firrtl.node %18 : !firrtl.uint<1>
  %assignWord = firrtl.wire : !firrtl.uint<16>
  %split_high = firrtl.wire : !firrtl.uint<8>
  %split_low = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %split_low, %c1_ui8 : !firrtl.uint<8>
  firrtl.strictconnect %split_high, %c255_ui8 : !firrtl.uint<8>
  %19 = firrtl.cat %split_high, %split_low : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<16>
  %_assignWord_T = firrtl.node %19 : !firrtl.uint<16>
  firrtl.strictconnect %assignWord, %_assignWord_T : !firrtl.uint<16>
  firrtl.strictconnect %io_word_6, %assignWord : !firrtl.uint<16>
  %vecResult_0 = firrtl.wire : !firrtl.uint<1>
  %vecResult_1 = firrtl.wire : !firrtl.uint<1>
  %vecResult_2 = firrtl.wire : !firrtl.uint<1>
  %vecResult_3 = firrtl.wire : !firrtl.uint<1>
  firrtl.strictconnect %vecResult_0, %c1_ui1 : !firrtl.uint<1>
  firrtl.strictconnect %vecResult_1, %c0_ui1 : !firrtl.uint<1>
  firrtl.strictconnect %vecResult_2, %c1_ui1 : !firrtl.uint<1>
  firrtl.strictconnect %vecResult_3, %c0_ui1 : !firrtl.uint<1>
  %20 = firrtl.cat %vecResult_1, %vecResult_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %uintResult_lo = firrtl.node %20 : !firrtl.uint<2>
  %21 = firrtl.cat %vecResult_3, %vecResult_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<2>
  %uintResult_hi = firrtl.node %21 : !firrtl.uint<2>
  %22 = firrtl.cat %uintResult_hi, %uintResult_lo : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<4>
  %uintResult = firrtl.node %22 : !firrtl.uint<4>
  firrtl.strictconnect %io_result_7, %uintResult : !firrtl.uint<4>
}

