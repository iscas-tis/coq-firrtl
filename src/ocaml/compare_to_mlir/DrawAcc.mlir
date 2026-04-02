// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @DrawAcc(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_din: !firrtl.uint<8>, in %io_sel: !firrtl.uint<3>, out %io_dout: !firrtl.uint<8>) attributes {convention = #firrtl<convention scalarized>} {
  %io_din_0 = firrtl.wire {name = "io_din"} : !firrtl.uint<8>
  %io_sel_1 = firrtl.wire {name = "io_sel"} : !firrtl.uint<3>
  %io_dout_2 = firrtl.wire {name = "io_dout"} : !firrtl.uint<8>
  firrtl.strictconnect %io_din_0, %io_din : !firrtl.uint<8>
  firrtl.strictconnect %io_sel_1, %io_sel : !firrtl.uint<3>
  firrtl.strictconnect %io_dout, %io_dout_2 : !firrtl.uint<8>
  %c0_ui8 = firrtl.constant 0 : !firrtl.uint<8>
  %regAcc = firrtl.regreset %clock, %reset1, %c0_ui8 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %0 = firrtl.eq %c0_ui1, %io_sel_1 : (!firrtl.uint<1>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %1 = firrtl.node %0 : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %c2_ui2 = firrtl.constant 2 : !firrtl.uint<2>
  %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
  %2 = firrtl.not %1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %3 = firrtl.eq %c1_ui1, %io_sel_1 : (!firrtl.uint<1>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %4 = firrtl.node %3 : !firrtl.uint<1>
  %5 = firrtl.and %2, %4 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %6 = firrtl.pad %c0_ui1, 8 : (!firrtl.uint<1>) -> !firrtl.uint<8>
  %7 = firrtl.not %4 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %8 = firrtl.and %2, %7 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %9 = firrtl.eq %c2_ui2, %io_sel_1 : (!firrtl.uint<2>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %10 = firrtl.node %9 : !firrtl.uint<1>
  %11 = firrtl.and %8, %10 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %12 = firrtl.add %regAcc, %io_din_0 : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<9>
  %_regAcc_T = firrtl.node %12 : !firrtl.uint<9>
  %13 = firrtl.tail %_regAcc_T, 1 : (!firrtl.uint<9>) -> !firrtl.uint<8>
  %_regAcc_T_1 = firrtl.node %13 : !firrtl.uint<8>
  %14 = firrtl.not %10 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %15 = firrtl.and %8, %14 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %16 = firrtl.eq %c3_ui2, %io_sel_1 : (!firrtl.uint<2>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %17 = firrtl.node %16 : !firrtl.uint<1>
  %18 = firrtl.and %15, %17 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %19 = firrtl.sub %regAcc, %io_din_0 : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<9>
  %_regAcc_T_2 = firrtl.node %19 : !firrtl.uint<9>
  %20 = firrtl.tail %_regAcc_T_2, 1 : (!firrtl.uint<9>) -> !firrtl.uint<8>
  %_regAcc_T_3 = firrtl.node %20 : !firrtl.uint<8>
  %21 = firrtl.mux(%17, %_regAcc_T_3, %regAcc) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %22 = firrtl.mux(%10, %_regAcc_T_1, %21) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %23 = firrtl.mux(%4, %6, %22) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %24 = firrtl.mux(%1, %regAcc, %23) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  firrtl.connect %regAcc, %24 : !firrtl.uint<8>, !firrtl.uint<8>
  firrtl.strictconnect %io_dout_2, %regAcc : !firrtl.uint<8>
}

