// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @RisingFsm(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_din: !firrtl.uint<1>, out %io_risingEdge: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_din_0 = firrtl.wire {name = "io_din"} : !firrtl.uint<1>
  %io_risingEdge_1 = firrtl.wire {name = "io_risingEdge"} : !firrtl.uint<1>
  firrtl.strictconnect %io_din_0, %io_din : !firrtl.uint<1>
  firrtl.strictconnect %io_risingEdge, %io_risingEdge_1 : !firrtl.uint<1>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %stateReg = firrtl.regreset %clock, %reset1, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>
  %0 = firrtl.asUInt %c0_ui1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %1 = firrtl.node %0 : !firrtl.uint<1>
  %2 = firrtl.asUInt %stateReg : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %3 = firrtl.node %2 : !firrtl.uint<1>
  %4 = firrtl.eq %1, %3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %5 = firrtl.node %4 : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %6 = firrtl.and %5, %io_din_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %7 = firrtl.mux(%io_din_0, %c1_ui1, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %8 = firrtl.mux(%5, %io_din_0, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.connect %io_risingEdge_1, %8 : !firrtl.uint<1>, !firrtl.uint<1>
  %9 = firrtl.not %5 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %10 = firrtl.asUInt %c1_ui1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %11 = firrtl.node %10 : !firrtl.uint<1>
  %12 = firrtl.node %2 : !firrtl.uint<1>
  %13 = firrtl.eq %11, %12 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %14 = firrtl.node %13 : !firrtl.uint<1>
  %15 = firrtl.and %9, %14 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %16 = firrtl.eq %io_din_0, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %17 = firrtl.node %16 : !firrtl.uint<1>
  %18 = firrtl.and %15, %17 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %19 = firrtl.mux(%17, %c0_ui1, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %20 = firrtl.mux(%14, %19, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %21 = firrtl.mux(%5, %7, %20) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.connect %stateReg, %21 : !firrtl.uint<1>, !firrtl.uint<1>
}

