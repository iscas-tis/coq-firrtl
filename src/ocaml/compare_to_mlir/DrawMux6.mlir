// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @DrawMux6(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_sel: !firrtl.uint<3>, out %io_dout: !firrtl.uint<8>) attributes {convention = #firrtl<convention scalarized>} {
  %io_sel_0 = firrtl.wire {name = "io_sel"} : !firrtl.uint<3>
  %io_dout_1 = firrtl.wire {name = "io_dout"} : !firrtl.uint<8>
  firrtl.strictconnect %io_sel_0, %io_sel : !firrtl.uint<3>
  firrtl.strictconnect %io_dout, %io_dout_1 : !firrtl.uint<8>
  %dout = firrtl.wire : !firrtl.uint<6>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %0 = firrtl.eq %c0_ui1, %io_sel_0 : (!firrtl.uint<1>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %1 = firrtl.node %0 : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %c11_ui4 = firrtl.constant 11 : !firrtl.uint<4>
  %c2_ui2 = firrtl.constant 2 : !firrtl.uint<2>
  %c22_ui5 = firrtl.constant 22 : !firrtl.uint<5>
  %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
  %c33_ui6 = firrtl.constant 33 : !firrtl.uint<6>
  %c4_ui3 = firrtl.constant 4 : !firrtl.uint<3>
  %c44_ui6 = firrtl.constant 44 : !firrtl.uint<6>
  %c5_ui3 = firrtl.constant 5 : !firrtl.uint<3>
  %c55_ui6 = firrtl.constant 55 : !firrtl.uint<6>
  %2 = firrtl.not %1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %3 = firrtl.eq %c1_ui1, %io_sel_0 : (!firrtl.uint<1>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %4 = firrtl.node %3 : !firrtl.uint<1>
  %5 = firrtl.and %2, %4 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %6 = firrtl.not %4 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %7 = firrtl.and %2, %6 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %8 = firrtl.eq %c2_ui2, %io_sel_0 : (!firrtl.uint<2>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %9 = firrtl.node %8 : !firrtl.uint<1>
  %10 = firrtl.and %7, %9 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %11 = firrtl.not %9 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %12 = firrtl.and %7, %11 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %13 = firrtl.eq %c3_ui2, %io_sel_0 : (!firrtl.uint<2>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %14 = firrtl.node %13 : !firrtl.uint<1>
  %15 = firrtl.and %12, %14 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %16 = firrtl.not %14 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %17 = firrtl.and %12, %16 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %18 = firrtl.eq %c4_ui3, %io_sel_0 : (!firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %19 = firrtl.node %18 : !firrtl.uint<1>
  %20 = firrtl.and %17, %19 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %21 = firrtl.not %19 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %22 = firrtl.and %17, %21 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %23 = firrtl.eq %c5_ui3, %io_sel_0 : (!firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %24 = firrtl.node %23 : !firrtl.uint<1>
  %25 = firrtl.and %22, %24 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %26 = firrtl.mux(%24, %c55_ui6, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<6>, !firrtl.uint<1>) -> !firrtl.uint<6>
  %27 = firrtl.mux(%19, %c44_ui6, %26) : (!firrtl.uint<1>, !firrtl.uint<6>, !firrtl.uint<6>) -> !firrtl.uint<6>
  %28 = firrtl.mux(%14, %c33_ui6, %27) : (!firrtl.uint<1>, !firrtl.uint<6>, !firrtl.uint<6>) -> !firrtl.uint<6>
  %29 = firrtl.mux(%9, %c22_ui5, %28) : (!firrtl.uint<1>, !firrtl.uint<5>, !firrtl.uint<6>) -> !firrtl.uint<6>
  %30 = firrtl.mux(%4, %c11_ui4, %29) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<6>) -> !firrtl.uint<6>
  %31 = firrtl.mux(%1, %c0_ui1, %30) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<6>) -> !firrtl.uint<6>
  firrtl.connect %dout, %31 : !firrtl.uint<6>, !firrtl.uint<6>
  firrtl.connect %io_dout_1, %dout : !firrtl.uint<8>, !firrtl.uint<6>
}

