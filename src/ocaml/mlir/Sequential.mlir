// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @Sequential(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_d: !firrtl.uint<4>, out %io_q: !firrtl.uint<4>, in %io_d2: !firrtl.uint<4>, out %io_q2: !firrtl.uint<4>, in %io_d3: !firrtl.uint<4>, out %io_q3: !firrtl.uint<4>, in %io_ena: !firrtl.uint<1>, out %io_q4: !firrtl.uint<4>, out %io_q5: !firrtl.uint<4>, out %io_q6: !firrtl.uint<4>, out %io_q7: !firrtl.uint<4>, in %io_riseIn: !firrtl.uint<1>, out %io_riseOut: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_d_0 = firrtl.wire {name = "io_d"} : !firrtl.uint<4>
  %io_q_1 = firrtl.wire {name = "io_q"} : !firrtl.uint<4>
  %io_d2_2 = firrtl.wire {name = "io_d2"} : !firrtl.uint<4>
  %io_q2_3 = firrtl.wire {name = "io_q2"} : !firrtl.uint<4>
  %io_d3_4 = firrtl.wire {name = "io_d3"} : !firrtl.uint<4>
  %io_q3_5 = firrtl.wire {name = "io_q3"} : !firrtl.uint<4>
  %io_ena_6 = firrtl.wire {name = "io_ena"} : !firrtl.uint<1>
  %io_q4_7 = firrtl.wire {name = "io_q4"} : !firrtl.uint<4>
  %io_q5_8 = firrtl.wire {name = "io_q5"} : !firrtl.uint<4>
  %io_q6_9 = firrtl.wire {name = "io_q6"} : !firrtl.uint<4>
  %io_q7_10 = firrtl.wire {name = "io_q7"} : !firrtl.uint<4>
  %io_riseIn_11 = firrtl.wire {name = "io_riseIn"} : !firrtl.uint<1>
  %io_riseOut_12 = firrtl.wire {name = "io_riseOut"} : !firrtl.uint<1>
  firrtl.strictconnect %io_d_0, %io_d : !firrtl.uint<4>
  firrtl.strictconnect %io_q, %io_q_1 : !firrtl.uint<4>
  firrtl.strictconnect %io_d2_2, %io_d2 : !firrtl.uint<4>
  firrtl.strictconnect %io_q2, %io_q2_3 : !firrtl.uint<4>
  firrtl.strictconnect %io_d3_4, %io_d3 : !firrtl.uint<4>
  firrtl.strictconnect %io_q3, %io_q3_5 : !firrtl.uint<4>
  firrtl.strictconnect %io_ena_6, %io_ena : !firrtl.uint<1>
  firrtl.strictconnect %io_q4, %io_q4_7 : !firrtl.uint<4>
  firrtl.strictconnect %io_q5, %io_q5_8 : !firrtl.uint<4>
  firrtl.strictconnect %io_q6, %io_q6_9 : !firrtl.uint<4>
  firrtl.strictconnect %io_q7, %io_q7_10 : !firrtl.uint<4>
  firrtl.strictconnect %io_riseIn_11, %io_riseIn : !firrtl.uint<1>
  firrtl.strictconnect %io_riseOut, %io_riseOut_12 : !firrtl.uint<1>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %q = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<4>
  firrtl.connect %q, %io_d_0 : !firrtl.uint<4>, !firrtl.uint<4>
  firrtl.connect %io_q_1, %q : !firrtl.uint<4>, !firrtl.uint<4>
  %delayReg = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<4>
  firrtl.strictconnect %delayReg, %io_d2_2 : !firrtl.uint<4>
  firrtl.strictconnect %io_q2_3, %delayReg : !firrtl.uint<4>
  %c0_ui4 = firrtl.constant 0 : !firrtl.uint<4>
  %valReg = firrtl.regreset %clock, %reset1, %c0_ui4 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>
  firrtl.strictconnect %valReg, %io_d3_4 : !firrtl.uint<4>
  firrtl.strictconnect %io_q3_5, %valReg : !firrtl.uint<4>
  %enableReg = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<4>
  %0 = firrtl.mux(%io_ena_6, %io_d3_4, %enableReg) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  firrtl.connect %enableReg, %0 : !firrtl.uint<4>, !firrtl.uint<4>
  firrtl.strictconnect %io_q4_7, %enableReg : !firrtl.uint<4>
  %resetEnableReg = firrtl.regreset %clock, %reset1, %c0_ui4 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>
  %1 = firrtl.mux(%io_ena_6, %io_d3_4, %resetEnableReg) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  firrtl.connect %resetEnableReg, %1 : !firrtl.uint<4>, !firrtl.uint<4>
  firrtl.strictconnect %io_q5_8, %resetEnableReg : !firrtl.uint<4>
  %enableReg2 = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<4>
  %2 = firrtl.mux(%io_ena_6, %io_d3_4, %enableReg2) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  firrtl.connect %enableReg2, %2 : !firrtl.uint<4>, !firrtl.uint<4>
  firrtl.strictconnect %io_q6_9, %enableReg2 : !firrtl.uint<4>
  %resetEnableReg2 = firrtl.regreset %clock, %reset1, %c0_ui4 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>
  %3 = firrtl.mux(%io_ena_6, %io_d3_4, %resetEnableReg2) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  firrtl.connect %resetEnableReg2, %3 : !firrtl.uint<4>, !firrtl.uint<4>
  firrtl.strictconnect %io_q7_10, %resetEnableReg2 : !firrtl.uint<4>
  %risingEdge_REG = firrtl.reg %clock : !firrtl.clock, !firrtl.uint<1>
  firrtl.connect %risingEdge_REG, %io_riseIn_11 : !firrtl.uint<1>, !firrtl.uint<1>
  %4 = firrtl.eq %risingEdge_REG, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_risingEdge_T = firrtl.node %4 : !firrtl.uint<1>
  %5 = firrtl.and %io_riseIn_11, %_risingEdge_T : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %risingEdge = firrtl.node %5 : !firrtl.uint<1>
  firrtl.strictconnect %io_riseOut_12, %risingEdge : !firrtl.uint<1>
}

