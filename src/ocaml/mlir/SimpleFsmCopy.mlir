// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @SimpleFsmCopy(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_badEvent: !firrtl.uint<1>, in %io_clear: !firrtl.uint<1>, out %io_ringBell: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_badEvent_0 = firrtl.wire {name = "io_badEvent"} : !firrtl.uint<1>
  %io_clear_1 = firrtl.wire {name = "io_clear"} : !firrtl.uint<1>
  %io_ringBell_2 = firrtl.wire {name = "io_ringBell"} : !firrtl.uint<1>
  firrtl.strictconnect %io_badEvent_0, %io_badEvent : !firrtl.uint<1>
  firrtl.strictconnect %io_clear_1, %io_clear : !firrtl.uint<1>
  firrtl.strictconnect %io_ringBell, %io_ringBell_2 : !firrtl.uint<1>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %stateReg = firrtl.regreset %clock, %reset1, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<2>
  %0 = firrtl.asUInt %c0_ui1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %1 = firrtl.node %0 : !firrtl.uint<1>
  %2 = firrtl.asUInt %stateReg : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %3 = firrtl.node %2 : !firrtl.uint<2>
  %4 = firrtl.eq %1, %3 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %5 = firrtl.node %4 : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %c2_ui2 = firrtl.constant 2 : !firrtl.uint<2>
  %6 = firrtl.and %5, %io_badEvent_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %7 = firrtl.pad %c1_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %8 = firrtl.mux(%io_badEvent_0, %7, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %9 = firrtl.not %5 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %10 = firrtl.asUInt %c1_ui1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %11 = firrtl.node %10 : !firrtl.uint<1>
  %12 = firrtl.node %2 : !firrtl.uint<2>
  %13 = firrtl.eq %11, %12 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %14 = firrtl.node %13 : !firrtl.uint<1>
  %15 = firrtl.and %9, %14 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %16 = firrtl.and %15, %io_badEvent_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %17 = firrtl.not %io_badEvent_0 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %18 = firrtl.and %15, %17 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %19 = firrtl.and %18, %io_clear_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %20 = firrtl.pad %c0_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %21 = firrtl.mux(%io_clear_1, %20, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %22 = firrtl.mux(%io_badEvent_0, %c2_ui2, %21) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %23 = firrtl.not %14 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %24 = firrtl.and %9, %23 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %25 = firrtl.asUInt %c2_ui2 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %26 = firrtl.node %25 : !firrtl.uint<2>
  %27 = firrtl.node %2 : !firrtl.uint<2>
  %28 = firrtl.eq %26, %27 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %29 = firrtl.node %28 : !firrtl.uint<1>
  %30 = firrtl.and %24, %29 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %31 = firrtl.and %30, %io_clear_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %32 = firrtl.pad %c0_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %33 = firrtl.mux(%io_clear_1, %32, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %34 = firrtl.mux(%29, %33, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %35 = firrtl.mux(%14, %22, %34) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %36 = firrtl.mux(%5, %8, %35) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  firrtl.connect %stateReg, %36 : !firrtl.uint<2>, !firrtl.uint<2>
  %37 = firrtl.eq %stateReg, %c2_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %_io_ringBell_T = firrtl.node %37 : !firrtl.uint<1>
  firrtl.strictconnect %io_ringBell_2, %_io_ringBell_T : !firrtl.uint<1>
}

