// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @Flasher2(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %io_start: !firrtl.uint<1>, out %io_light: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_start_0 = firrtl.wire {name = "io_start"} : !firrtl.uint<1>
  %io_light_1 = firrtl.wire {name = "io_light"} : !firrtl.uint<1>
  firrtl.strictconnect %io_start_0, %io_start : !firrtl.uint<1>
  firrtl.strictconnect %io_light, %io_light_1 : !firrtl.uint<1>
  %0 = firrtl.bits %io_start_0 0 to 0 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %start = firrtl.node %0 : !firrtl.uint<1>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %stateReg = firrtl.regreset %clock, %reset, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<2>
  %light = firrtl.wire : !firrtl.uint<1>
  %timerLoad = firrtl.wire : !firrtl.uint<1>
  %timerSelect = firrtl.wire : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %timerDone = firrtl.wire : !firrtl.uint<1>
  %cntLoad = firrtl.wire : !firrtl.uint<1>
  %cntDecr = firrtl.wire : !firrtl.uint<1>
  %cntDone = firrtl.wire : !firrtl.uint<1>
  %1 = firrtl.asUInt %c0_ui1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %2 = firrtl.node %1 : !firrtl.uint<1>
  %3 = firrtl.asUInt %stateReg : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %4 = firrtl.node %3 : !firrtl.uint<2>
  %5 = firrtl.eq %2, %4 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %6 = firrtl.node %5 : !firrtl.uint<1>
  %c2_ui2 = firrtl.constant 2 : !firrtl.uint<2>
  %7 = firrtl.mux(%6, %c1_ui1, %timerDone) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.connect %timerLoad, %7 : !firrtl.uint<1>, !firrtl.uint<1>
  firrtl.connect %cntLoad, %6 : !firrtl.uint<1>, !firrtl.uint<1>
  %8 = firrtl.and %6, %start : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %9 = firrtl.pad %c1_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %10 = firrtl.mux(%start, %9, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %11 = firrtl.not %6 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %12 = firrtl.asUInt %c1_ui1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %13 = firrtl.node %12 : !firrtl.uint<1>
  %14 = firrtl.node %3 : !firrtl.uint<2>
  %15 = firrtl.eq %13, %14 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %16 = firrtl.node %15 : !firrtl.uint<1>
  %17 = firrtl.and %11, %16 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %18 = firrtl.mux(%16, %c0_ui1, %c1_ui1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %19 = firrtl.mux(%6, %c1_ui1, %18) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.connect %timerSelect, %19 : !firrtl.uint<1>, !firrtl.uint<1>
  %20 = firrtl.mux(%6, %c0_ui1, %16) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.connect %light, %20 : !firrtl.uint<1>, !firrtl.uint<1>
  %21 = firrtl.eq %cntDone, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %22 = firrtl.node %21 : !firrtl.uint<1>
  %23 = firrtl.and %timerDone, %22 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %24 = firrtl.node %23 : !firrtl.uint<1>
  %25 = firrtl.and %17, %24 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %26 = firrtl.mux(%24, %c2_ui2, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %27 = firrtl.and %timerDone, %cntDone : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %28 = firrtl.node %27 : !firrtl.uint<1>
  %29 = firrtl.and %17, %28 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %30 = firrtl.pad %c0_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %31 = firrtl.mux(%28, %30, %26) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %32 = firrtl.not %16 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %33 = firrtl.and %11, %32 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %34 = firrtl.asUInt %c2_ui2 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %35 = firrtl.node %34 : !firrtl.uint<2>
  %36 = firrtl.node %3 : !firrtl.uint<2>
  %37 = firrtl.eq %35, %36 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %38 = firrtl.node %37 : !firrtl.uint<1>
  %39 = firrtl.and %33, %38 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %40 = firrtl.mux(%38, %timerDone, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %41 = firrtl.mux(%16, %c0_ui1, %40) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %42 = firrtl.mux(%6, %c0_ui1, %41) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.connect %cntDecr, %42 : !firrtl.uint<1>, !firrtl.uint<1>
  %43 = firrtl.and %39, %timerDone : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %44 = firrtl.pad %c1_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %45 = firrtl.mux(%timerDone, %44, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %46 = firrtl.mux(%38, %45, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %47 = firrtl.mux(%16, %31, %46) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %48 = firrtl.mux(%6, %10, %47) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  firrtl.connect %stateReg, %48 : !firrtl.uint<2>, !firrtl.uint<2>
  %cntReg = firrtl.regreset %clock, %reset, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<2>
  %49 = firrtl.eq %cntReg, %c0_ui1 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_cntDone_T = firrtl.node %49 : !firrtl.uint<1>
  firrtl.strictconnect %cntDone, %_cntDone_T : !firrtl.uint<1>
  %50 = firrtl.mux(%cntLoad, %c2_ui2, %cntReg) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %51 = firrtl.sub %cntReg, %c1_ui1 : (!firrtl.uint<2>, !firrtl.uint<1>) -> !firrtl.uint<3>
  %_cntReg_T = firrtl.node %51 : !firrtl.uint<3>
  %52 = firrtl.tail %_cntReg_T, 1 : (!firrtl.uint<3>) -> !firrtl.uint<2>
  %_cntReg_T_1 = firrtl.node %52 : !firrtl.uint<2>
  %53 = firrtl.mux(%cntDecr, %_cntReg_T_1, %50) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  firrtl.connect %cntReg, %53 : !firrtl.uint<2>, !firrtl.uint<2>
  %timerReg = firrtl.regreset %clock, %reset, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<3>
  %54 = firrtl.eq %timerReg, %c0_ui1 : (!firrtl.uint<3>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_timerDone_T = firrtl.node %54 : !firrtl.uint<1>
  firrtl.strictconnect %timerDone, %_timerDone_T : !firrtl.uint<1>
  %55 = firrtl.eq %timerDone, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %56 = firrtl.node %55 : !firrtl.uint<1>
  %57 = firrtl.sub %timerReg, %c1_ui1 : (!firrtl.uint<3>, !firrtl.uint<1>) -> !firrtl.uint<4>
  %_timerReg_T = firrtl.node %57 : !firrtl.uint<4>
  %58 = firrtl.tail %_timerReg_T, 1 : (!firrtl.uint<4>) -> !firrtl.uint<3>
  %_timerReg_T_1 = firrtl.node %58 : !firrtl.uint<3>
  %59 = firrtl.mux(%56, %_timerReg_T_1, %timerReg) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %c5_ui3 = firrtl.constant 5 : !firrtl.uint<3>
  %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
  %60 = firrtl.and %timerLoad, %timerSelect : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %61 = firrtl.not %timerSelect : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %62 = firrtl.and %timerLoad, %61 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %63 = firrtl.mux(%timerSelect, %c5_ui3, %c3_ui2) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<2>) -> !firrtl.uint<3>
  %64 = firrtl.mux(%timerLoad, %63, %59) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  firrtl.connect %timerReg, %64 : !firrtl.uint<3>, !firrtl.uint<3>
  firrtl.strictconnect %io_light_1, %light : !firrtl.uint<1>
}

