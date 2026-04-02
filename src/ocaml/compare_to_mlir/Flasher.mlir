// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @Flasher(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %io_start: !firrtl.uint<1>, out %io_light: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_start_0 = firrtl.wire {name = "io_start"} : !firrtl.uint<1>
  %io_light_1 = firrtl.wire {name = "io_light"} : !firrtl.uint<1>
  firrtl.strictconnect %io_start_0, %io_start : !firrtl.uint<1>
  firrtl.strictconnect %io_light, %io_light_1 : !firrtl.uint<1>
  %0 = firrtl.bits %io_start_0 0 to 0 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %start = firrtl.node %0 : !firrtl.uint<1>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %stateReg = firrtl.regreset %clock, %reset, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<3>
  %light = firrtl.wire : !firrtl.uint<1>
  %timerLoad = firrtl.wire : !firrtl.uint<1>
  %timerSelect = firrtl.wire : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %timerDone = firrtl.wire : !firrtl.uint<1>
  %1 = firrtl.asUInt %c0_ui1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %2 = firrtl.node %1 : !firrtl.uint<1>
  %3 = firrtl.asUInt %stateReg : (!firrtl.uint<3>) -> !firrtl.uint<3>
  %4 = firrtl.node %3 : !firrtl.uint<3>
  %5 = firrtl.eq %2, %4 : (!firrtl.uint<1>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %6 = firrtl.node %5 : !firrtl.uint<1>
  %c2_ui2 = firrtl.constant 2 : !firrtl.uint<2>
  %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
  %c4_ui3 = firrtl.constant 4 : !firrtl.uint<3>
  %c5_ui3 = firrtl.constant 5 : !firrtl.uint<3>
  %7 = firrtl.mux(%6, %c1_ui1, %timerDone) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.connect %timerLoad, %7 : !firrtl.uint<1>, !firrtl.uint<1>
  %8 = firrtl.and %6, %start : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %9 = firrtl.pad %c1_ui1, 3 : (!firrtl.uint<1>) -> !firrtl.uint<3>
  %10 = firrtl.mux(%start, %9, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %11 = firrtl.not %6 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %12 = firrtl.asUInt %c1_ui1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %13 = firrtl.node %12 : !firrtl.uint<1>
  %14 = firrtl.node %3 : !firrtl.uint<3>
  %15 = firrtl.eq %13, %14 : (!firrtl.uint<1>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %16 = firrtl.node %15 : !firrtl.uint<1>
  %17 = firrtl.and %11, %16 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %18 = firrtl.and %17, %timerDone : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %19 = firrtl.pad %c2_ui2, 3 : (!firrtl.uint<2>) -> !firrtl.uint<3>
  %20 = firrtl.mux(%timerDone, %19, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %21 = firrtl.not %16 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %22 = firrtl.and %11, %21 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %23 = firrtl.asUInt %c2_ui2 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %24 = firrtl.node %23 : !firrtl.uint<2>
  %25 = firrtl.node %3 : !firrtl.uint<3>
  %26 = firrtl.eq %24, %25 : (!firrtl.uint<2>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %27 = firrtl.node %26 : !firrtl.uint<1>
  %28 = firrtl.and %22, %27 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %29 = firrtl.and %28, %timerDone : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %30 = firrtl.pad %c3_ui2, 3 : (!firrtl.uint<2>) -> !firrtl.uint<3>
  %31 = firrtl.mux(%timerDone, %30, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %32 = firrtl.not %27 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %33 = firrtl.and %22, %32 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %34 = firrtl.asUInt %c3_ui2 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %35 = firrtl.node %34 : !firrtl.uint<2>
  %36 = firrtl.node %3 : !firrtl.uint<3>
  %37 = firrtl.eq %35, %36 : (!firrtl.uint<2>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %38 = firrtl.node %37 : !firrtl.uint<1>
  %39 = firrtl.and %33, %38 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %40 = firrtl.and %39, %timerDone : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %41 = firrtl.mux(%timerDone, %c4_ui3, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %42 = firrtl.not %38 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %43 = firrtl.and %33, %42 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %44 = firrtl.asUInt %c4_ui3 : (!firrtl.uint<3>) -> !firrtl.uint<3>
  %45 = firrtl.node %44 : !firrtl.uint<3>
  %46 = firrtl.node %3 : !firrtl.uint<3>
  %47 = firrtl.eq %45, %46 : (!firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %48 = firrtl.node %47 : !firrtl.uint<1>
  %49 = firrtl.and %43, %48 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %50 = firrtl.and %49, %timerDone : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %51 = firrtl.mux(%timerDone, %c5_ui3, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %52 = firrtl.not %48 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %53 = firrtl.and %43, %52 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %54 = firrtl.asUInt %c5_ui3 : (!firrtl.uint<3>) -> !firrtl.uint<3>
  %55 = firrtl.node %54 : !firrtl.uint<3>
  %56 = firrtl.node %3 : !firrtl.uint<3>
  %57 = firrtl.eq %55, %56 : (!firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %58 = firrtl.node %57 : !firrtl.uint<1>
  %59 = firrtl.and %53, %58 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %60 = firrtl.mux(%58, %c0_ui1, %c1_ui1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %61 = firrtl.mux(%48, %c1_ui1, %60) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %62 = firrtl.mux(%38, %c0_ui1, %61) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %63 = firrtl.mux(%27, %c1_ui1, %62) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %64 = firrtl.mux(%16, %c0_ui1, %63) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %65 = firrtl.mux(%6, %c1_ui1, %64) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.connect %timerSelect, %65 : !firrtl.uint<1>, !firrtl.uint<1>
  %66 = firrtl.mux(%48, %c0_ui1, %58) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %67 = firrtl.mux(%38, %c1_ui1, %66) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %68 = firrtl.mux(%27, %c0_ui1, %67) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %69 = firrtl.mux(%16, %c1_ui1, %68) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %70 = firrtl.mux(%6, %c0_ui1, %69) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.connect %light, %70 : !firrtl.uint<1>, !firrtl.uint<1>
  %71 = firrtl.and %59, %timerDone : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %72 = firrtl.pad %c0_ui1, 3 : (!firrtl.uint<1>) -> !firrtl.uint<3>
  %73 = firrtl.mux(%timerDone, %72, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %74 = firrtl.mux(%58, %73, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %75 = firrtl.mux(%48, %51, %74) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %76 = firrtl.mux(%38, %41, %75) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %77 = firrtl.mux(%27, %31, %76) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %78 = firrtl.mux(%16, %20, %77) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %79 = firrtl.mux(%6, %10, %78) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  firrtl.connect %stateReg, %79 : !firrtl.uint<3>, !firrtl.uint<3>
  %timerReg = firrtl.regreset %clock, %reset, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<3>
  %80 = firrtl.eq %timerReg, %c0_ui1 : (!firrtl.uint<3>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_timerDone_T = firrtl.node %80 : !firrtl.uint<1>
  firrtl.strictconnect %timerDone, %_timerDone_T : !firrtl.uint<1>
  %81 = firrtl.eq %timerDone, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %82 = firrtl.node %81 : !firrtl.uint<1>
  %83 = firrtl.sub %timerReg, %c1_ui1 : (!firrtl.uint<3>, !firrtl.uint<1>) -> !firrtl.uint<4>
  %_timerReg_T = firrtl.node %83 : !firrtl.uint<4>
  %84 = firrtl.tail %_timerReg_T, 1 : (!firrtl.uint<4>) -> !firrtl.uint<3>
  %_timerReg_T_1 = firrtl.node %84 : !firrtl.uint<3>
  %85 = firrtl.mux(%82, %_timerReg_T_1, %timerReg) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %86 = firrtl.and %timerLoad, %timerSelect : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %87 = firrtl.not %timerSelect : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %88 = firrtl.and %timerLoad, %87 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %89 = firrtl.mux(%timerSelect, %c5_ui3, %c3_ui2) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<2>) -> !firrtl.uint<3>
  %90 = firrtl.mux(%timerLoad, %89, %85) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  firrtl.connect %timerReg, %90 : !firrtl.uint<3>, !firrtl.uint<3>
  firrtl.strictconnect %io_light_1, %light : !firrtl.uint<1>
}

