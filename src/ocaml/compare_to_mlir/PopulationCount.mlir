// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @PopulationCount(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %io_dinValid: !firrtl.uint<1>, out %io_dinReady: !firrtl.uint<1>, in %io_din: !firrtl.uint<8>, out %io_popCntValid: !firrtl.uint<1>, in %io_popCntReady: !firrtl.uint<1>, out %io_popCnt: !firrtl.uint<4>) attributes {convention = #firrtl<convention scalarized>} {
  %io_dinValid_0 = firrtl.wire {name = "io_dinValid"} : !firrtl.uint<1>
  %io_dinReady_1 = firrtl.wire {name = "io_dinReady"} : !firrtl.uint<1>
  %io_din_2 = firrtl.wire {name = "io_din"} : !firrtl.uint<8>
  %io_popCntValid_3 = firrtl.wire {name = "io_popCntValid"} : !firrtl.uint<1>
  %io_popCntReady_4 = firrtl.wire {name = "io_popCntReady"} : !firrtl.uint<1>
  %io_popCnt_5 = firrtl.wire {name = "io_popCnt"} : !firrtl.uint<4>
  firrtl.strictconnect %io_dinValid_0, %io_dinValid : !firrtl.uint<1>
  firrtl.strictconnect %io_dinReady, %io_dinReady_1 : !firrtl.uint<1>
  firrtl.strictconnect %io_din_2, %io_din : !firrtl.uint<8>
  firrtl.strictconnect %io_popCntValid, %io_popCntValid_3 : !firrtl.uint<1>
  firrtl.strictconnect %io_popCntReady_4, %io_popCntReady : !firrtl.uint<1>
  firrtl.strictconnect %io_popCnt, %io_popCnt_5 : !firrtl.uint<4>
  %fsm_clock, %fsm_reset, %fsm_io_dinValid, %fsm_io_dinReady, %fsm_io_popCntValid, %fsm_io_popCntReady, %fsm_io_load, %fsm_io_done = firrtl.instance fsm @PopCountFSM(in clock: !firrtl.clock, in reset: !firrtl.uint<1>, in io_dinValid: !firrtl.uint<1>, out io_dinReady: !firrtl.uint<1>, out io_popCntValid: !firrtl.uint<1>, in io_popCntReady: !firrtl.uint<1>, out io_load: !firrtl.uint<1>, in io_done: !firrtl.uint<1>)
  %fsm.io_dinValid = firrtl.wire : !firrtl.uint<1>
  %fsm.io_dinReady = firrtl.wire : !firrtl.uint<1>
  %fsm.io_popCntValid = firrtl.wire : !firrtl.uint<1>
  %fsm.io_popCntReady = firrtl.wire : !firrtl.uint<1>
  %fsm.io_load = firrtl.wire : !firrtl.uint<1>
  %fsm.io_done = firrtl.wire : !firrtl.uint<1>
  firrtl.strictconnect %fsm_io_dinValid, %fsm.io_dinValid : !firrtl.uint<1>
  firrtl.strictconnect %fsm.io_dinReady, %fsm_io_dinReady : !firrtl.uint<1>
  firrtl.strictconnect %fsm.io_popCntValid, %fsm_io_popCntValid : !firrtl.uint<1>
  firrtl.strictconnect %fsm_io_popCntReady, %fsm.io_popCntReady : !firrtl.uint<1>
  firrtl.strictconnect %fsm.io_load, %fsm_io_load : !firrtl.uint<1>
  firrtl.strictconnect %fsm_io_done, %fsm.io_done : !firrtl.uint<1>
  firrtl.strictconnect %fsm_clock, %clock : !firrtl.clock
  firrtl.strictconnect %fsm_reset, %reset : !firrtl.uint<1>
  %data_clock, %data_reset, %data_io_din, %data_io_load, %data_io_popCnt, %data_io_done = firrtl.instance data @PopCountDataPath(in clock: !firrtl.clock, in reset: !firrtl.uint<1>, in io_din: !firrtl.uint<8>, in io_load: !firrtl.uint<1>, out io_popCnt: !firrtl.uint<4>, out io_done: !firrtl.uint<1>)
  %data.io_din = firrtl.wire : !firrtl.uint<8>
  %data.io_load = firrtl.wire : !firrtl.uint<1>
  %data.io_popCnt = firrtl.wire : !firrtl.uint<4>
  %data.io_done = firrtl.wire : !firrtl.uint<1>
  firrtl.strictconnect %data_io_din, %data.io_din : !firrtl.uint<8>
  firrtl.strictconnect %data_io_load, %data.io_load : !firrtl.uint<1>
  firrtl.strictconnect %data.io_popCnt, %data_io_popCnt : !firrtl.uint<4>
  firrtl.strictconnect %data.io_done, %data_io_done : !firrtl.uint<1>
  firrtl.strictconnect %data_clock, %clock : !firrtl.clock
  firrtl.strictconnect %data_reset, %reset : !firrtl.uint<1>
  firrtl.strictconnect %fsm.io_dinValid, %io_dinValid_0 : !firrtl.uint<1>
  firrtl.strictconnect %io_dinReady_1, %fsm.io_dinReady : !firrtl.uint<1>
  firrtl.strictconnect %io_popCntValid_3, %fsm.io_popCntValid : !firrtl.uint<1>
  firrtl.strictconnect %fsm.io_popCntReady, %io_popCntReady_4 : !firrtl.uint<1>
  firrtl.strictconnect %data.io_din, %io_din_2 : !firrtl.uint<8>
  firrtl.strictconnect %io_popCnt_5, %data.io_popCnt : !firrtl.uint<4>
  firrtl.strictconnect %data.io_load, %fsm.io_load : !firrtl.uint<1>
  firrtl.strictconnect %fsm.io_done, %data.io_done : !firrtl.uint<1>
}

// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module private @PopCountFSM(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %io_dinValid: !firrtl.uint<1>, out %io_dinReady: !firrtl.uint<1>, out %io_popCntValid: !firrtl.uint<1>, in %io_popCntReady: !firrtl.uint<1>, out %io_load: !firrtl.uint<1>, in %io_done: !firrtl.uint<1>) {
  %io_dinValid_0 = firrtl.wire {name = "io_dinValid"} : !firrtl.uint<1>
  %io_dinReady_1 = firrtl.wire {name = "io_dinReady"} : !firrtl.uint<1>
  %io_popCntValid_2 = firrtl.wire {name = "io_popCntValid"} : !firrtl.uint<1>
  %io_popCntReady_3 = firrtl.wire {name = "io_popCntReady"} : !firrtl.uint<1>
  %io_load_4 = firrtl.wire {name = "io_load"} : !firrtl.uint<1>
  %io_done_5 = firrtl.wire {name = "io_done"} : !firrtl.uint<1>
  firrtl.strictconnect %io_dinValid_0, %io_dinValid : !firrtl.uint<1>
  firrtl.strictconnect %io_dinReady, %io_dinReady_1 : !firrtl.uint<1>
  firrtl.strictconnect %io_popCntValid, %io_popCntValid_2 : !firrtl.uint<1>
  firrtl.strictconnect %io_popCntReady_3, %io_popCntReady : !firrtl.uint<1>
  firrtl.strictconnect %io_load, %io_load_4 : !firrtl.uint<1>
  firrtl.strictconnect %io_done_5, %io_done : !firrtl.uint<1>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %stateReg = firrtl.regreset %clock, %reset, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<2>
  %0 = firrtl.asUInt %c0_ui1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %1 = firrtl.node %0 : !firrtl.uint<1>
  %2 = firrtl.asUInt %stateReg : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %3 = firrtl.node %2 : !firrtl.uint<2>
  %4 = firrtl.eq %1, %3 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %5 = firrtl.node %4 : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %c2_ui2 = firrtl.constant 2 : !firrtl.uint<2>
  firrtl.connect %io_dinReady_1, %5 : !firrtl.uint<1>, !firrtl.uint<1>
  %6 = firrtl.and %5, %io_dinValid_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %7 = firrtl.mux(%5, %io_dinValid_0, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.connect %io_load_4, %7 : !firrtl.uint<1>, !firrtl.uint<1>
  %8 = firrtl.pad %c1_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %9 = firrtl.mux(%io_dinValid_0, %8, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %10 = firrtl.not %5 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %11 = firrtl.asUInt %c1_ui1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %12 = firrtl.node %11 : !firrtl.uint<1>
  %13 = firrtl.node %2 : !firrtl.uint<2>
  %14 = firrtl.eq %12, %13 : (!firrtl.uint<1>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %15 = firrtl.node %14 : !firrtl.uint<1>
  %16 = firrtl.and %10, %15 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %17 = firrtl.and %16, %io_done_5 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %18 = firrtl.mux(%io_done_5, %c2_ui2, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %19 = firrtl.not %15 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %20 = firrtl.and %10, %19 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %21 = firrtl.asUInt %c2_ui2 : (!firrtl.uint<2>) -> !firrtl.uint<2>
  %22 = firrtl.node %21 : !firrtl.uint<2>
  %23 = firrtl.node %2 : !firrtl.uint<2>
  %24 = firrtl.eq %22, %23 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
  %25 = firrtl.node %24 : !firrtl.uint<1>
  %26 = firrtl.and %20, %25 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %27 = firrtl.mux(%15, %c0_ui1, %25) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %28 = firrtl.mux(%5, %c0_ui1, %27) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.connect %io_popCntValid_2, %28 : !firrtl.uint<1>, !firrtl.uint<1>
  %29 = firrtl.and %26, %io_popCntReady_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %30 = firrtl.pad %c0_ui1, 2 : (!firrtl.uint<1>) -> !firrtl.uint<2>
  %31 = firrtl.mux(%io_popCntReady_3, %30, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %32 = firrtl.mux(%25, %31, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %33 = firrtl.mux(%15, %18, %32) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  %34 = firrtl.mux(%5, %9, %33) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
  firrtl.connect %stateReg, %34 : !firrtl.uint<2>, !firrtl.uint<2>
}

// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module private @PopCountDataPath(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %io_din: !firrtl.uint<8>, in %io_load: !firrtl.uint<1>, out %io_popCnt: !firrtl.uint<4>, out %io_done: !firrtl.uint<1>) {
  %io_din_0 = firrtl.wire {name = "io_din"} : !firrtl.uint<8>
  %io_load_1 = firrtl.wire {name = "io_load"} : !firrtl.uint<1>
  %io_popCnt_2 = firrtl.wire {name = "io_popCnt"} : !firrtl.uint<4>
  %io_done_3 = firrtl.wire {name = "io_done"} : !firrtl.uint<1>
  firrtl.strictconnect %io_din_0, %io_din : !firrtl.uint<8>
  firrtl.strictconnect %io_load_1, %io_load : !firrtl.uint<1>
  firrtl.strictconnect %io_popCnt, %io_popCnt_2 : !firrtl.uint<4>
  firrtl.strictconnect %io_done, %io_done_3 : !firrtl.uint<1>
  %c0_ui8 = firrtl.constant 0 : !firrtl.uint<8>
  %dataReg = firrtl.regreset %clock, %reset, %c0_ui8 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>
  %popCntReg = firrtl.regreset %clock, %reset, %c0_ui8 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>
  %c0_ui4 = firrtl.constant 0 : !firrtl.uint<4>
  %counterReg = firrtl.regreset %clock, %reset, %c0_ui4 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>
  %0 = firrtl.bits %dataReg 7 to 1 : (!firrtl.uint<8>) -> !firrtl.uint<7>
  %_dataReg_T = firrtl.node %0 : !firrtl.uint<7>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %1 = firrtl.cat %c0_ui1, %_dataReg_T : (!firrtl.uint<1>, !firrtl.uint<7>) -> !firrtl.uint<8>
  %_dataReg_T_1 = firrtl.node %1 : !firrtl.uint<8>
  %2 = firrtl.bits %dataReg 0 to 0 : (!firrtl.uint<8>) -> !firrtl.uint<1>
  %_popCntReg_T = firrtl.node %2 : !firrtl.uint<1>
  %3 = firrtl.add %popCntReg, %_popCntReg_T : (!firrtl.uint<8>, !firrtl.uint<1>) -> !firrtl.uint<9>
  %_popCntReg_T_1 = firrtl.node %3 : !firrtl.uint<9>
  %4 = firrtl.tail %_popCntReg_T_1, 1 : (!firrtl.uint<9>) -> !firrtl.uint<8>
  %_popCntReg_T_2 = firrtl.node %4 : !firrtl.uint<8>
  %5 = firrtl.eq %counterReg, %c0_ui1 : (!firrtl.uint<4>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %done = firrtl.node %5 : !firrtl.uint<1>
  %6 = firrtl.eq %done, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %7 = firrtl.node %6 : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %8 = firrtl.sub %counterReg, %c1_ui1 : (!firrtl.uint<4>, !firrtl.uint<1>) -> !firrtl.uint<5>
  %_counterReg_T = firrtl.node %8 : !firrtl.uint<5>
  %9 = firrtl.tail %_counterReg_T, 1 : (!firrtl.uint<5>) -> !firrtl.uint<4>
  %_counterReg_T_1 = firrtl.node %9 : !firrtl.uint<4>
  %10 = firrtl.mux(%7, %_counterReg_T_1, %counterReg) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  %c8_ui4 = firrtl.constant 8 : !firrtl.uint<4>
  %11 = firrtl.mux(%io_load_1, %io_din_0, %_dataReg_T_1) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  firrtl.connect %dataReg, %11 : !firrtl.uint<8>, !firrtl.uint<8>
  %12 = firrtl.pad %c0_ui1, 8 : (!firrtl.uint<1>) -> !firrtl.uint<8>
  %13 = firrtl.mux(%io_load_1, %12, %_popCntReg_T_2) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  firrtl.connect %popCntReg, %13 : !firrtl.uint<8>, !firrtl.uint<8>
  %14 = firrtl.mux(%io_load_1, %c8_ui4, %10) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  firrtl.connect %counterReg, %14 : !firrtl.uint<4>, !firrtl.uint<4>
  %15 = firrtl.asUInt %reset : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %16 = firrtl.node %15 : !firrtl.uint<1>
  %17 = firrtl.eq %16, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %18 = firrtl.node %17 : !firrtl.uint<1>
  firrtl.printf %clock, %18, "%x %d\0A" {name = "printf"} (%dataReg, %popCntReg) : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>
  %19 = firrtl.tail %popCntReg, 4 : (!firrtl.uint<8>) -> !firrtl.uint<4>
  firrtl.strictconnect %io_popCnt_2, %19 : !firrtl.uint<4>
  firrtl.strictconnect %io_done_3, %done : !firrtl.uint<1>
}

