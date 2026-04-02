// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module private @NocRouter2(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %io_inPort_0_address: !firrtl.uint<8>, in %io_inPort_0_data_data: !firrtl.uint<16>, in %io_inPort_0_data_flag: !firrtl.uint<1>, in %io_inPort_1_address: !firrtl.uint<8>, in %io_inPort_1_data_data: !firrtl.uint<16>, in %io_inPort_1_data_flag: !firrtl.uint<1>, out %io_outPort_0_address: !firrtl.uint<8>, out %io_outPort_0_data_data: !firrtl.uint<16>, out %io_outPort_0_data_flag: !firrtl.uint<1>, out %io_outPort_1_address: !firrtl.uint<8>, out %io_outPort_1_data_data: !firrtl.uint<16>, out %io_outPort_1_data_flag: !firrtl.uint<1>) {
  %io_inPort_0_address_0 = firrtl.wire {name = "io_inPort_0_address"} : !firrtl.uint<8>
  %io_inPort_0_data_data_1 = firrtl.wire {name = "io_inPort_0_data_data"} : !firrtl.uint<16>
  %io_inPort_0_data_flag_2 = firrtl.wire {name = "io_inPort_0_data_flag"} : !firrtl.uint<1>
  %io_inPort_1_address_3 = firrtl.wire {name = "io_inPort_1_address"} : !firrtl.uint<8>
  %io_inPort_1_data_data_4 = firrtl.wire {name = "io_inPort_1_data_data"} : !firrtl.uint<16>
  %io_inPort_1_data_flag_5 = firrtl.wire {name = "io_inPort_1_data_flag"} : !firrtl.uint<1>
  %io_outPort_0_address_6 = firrtl.wire {name = "io_outPort_0_address"} : !firrtl.uint<8>
  %io_outPort_0_data_data_7 = firrtl.wire {name = "io_outPort_0_data_data"} : !firrtl.uint<16>
  %io_outPort_0_data_flag_8 = firrtl.wire {name = "io_outPort_0_data_flag"} : !firrtl.uint<1>
  %io_outPort_1_address_9 = firrtl.wire {name = "io_outPort_1_address"} : !firrtl.uint<8>
  %io_outPort_1_data_data_10 = firrtl.wire {name = "io_outPort_1_data_data"} : !firrtl.uint<16>
  %io_outPort_1_data_flag_11 = firrtl.wire {name = "io_outPort_1_data_flag"} : !firrtl.uint<1>
  firrtl.strictconnect %io_inPort_0_address_0, %io_inPort_0_address : !firrtl.uint<8>
  firrtl.strictconnect %io_inPort_0_data_data_1, %io_inPort_0_data_data : !firrtl.uint<16>
  firrtl.strictconnect %io_inPort_0_data_flag_2, %io_inPort_0_data_flag : !firrtl.uint<1>
  firrtl.strictconnect %io_inPort_1_address_3, %io_inPort_1_address : !firrtl.uint<8>
  firrtl.strictconnect %io_inPort_1_data_data_4, %io_inPort_1_data_data : !firrtl.uint<16>
  firrtl.strictconnect %io_inPort_1_data_flag_5, %io_inPort_1_data_flag : !firrtl.uint<1>
  firrtl.strictconnect %io_outPort_0_address, %io_outPort_0_address_6 : !firrtl.uint<8>
  firrtl.strictconnect %io_outPort_0_data_data, %io_outPort_0_data_data_7 : !firrtl.uint<16>
  firrtl.strictconnect %io_outPort_0_data_flag, %io_outPort_0_data_flag_8 : !firrtl.uint<1>
  firrtl.strictconnect %io_outPort_1_address, %io_outPort_1_address_9 : !firrtl.uint<8>
  firrtl.strictconnect %io_outPort_1_data_data, %io_outPort_1_data_data_10 : !firrtl.uint<16>
  firrtl.strictconnect %io_outPort_1_data_flag, %io_outPort_1_data_flag_11 : !firrtl.uint<1>
  firrtl.strictconnect %io_outPort_0_address_6, %io_inPort_1_address_3 : !firrtl.uint<8>
  firrtl.strictconnect %io_outPort_0_data_data_7, %io_inPort_1_data_data_4 : !firrtl.uint<16>
  firrtl.strictconnect %io_outPort_0_data_flag_8, %io_inPort_1_data_flag_5 : !firrtl.uint<1>
  firrtl.strictconnect %io_outPort_1_address_9, %io_inPort_0_address_0 : !firrtl.uint<8>
  firrtl.strictconnect %io_outPort_1_data_data_10, %io_inPort_0_data_data_1 : !firrtl.uint<16>
  firrtl.strictconnect %io_outPort_1_data_flag_11, %io_inPort_0_data_flag_2 : !firrtl.uint<1>
}

// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @UseParamRouter2(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %io_in_data: !firrtl.uint<16>, in %io_in_flag: !firrtl.uint<1>, in %io_inAddr: !firrtl.uint<8>, out %io_outA_data: !firrtl.uint<16>, out %io_outA_flag: !firrtl.uint<1>, out %io_outB_data: !firrtl.uint<16>, out %io_outB_flag: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_in_data_0 = firrtl.wire {name = "io_in_data"} : !firrtl.uint<16>
  %io_in_flag_1 = firrtl.wire {name = "io_in_flag"} : !firrtl.uint<1>
  %io_inAddr_2 = firrtl.wire {name = "io_inAddr"} : !firrtl.uint<8>
  %io_outA_data_3 = firrtl.wire {name = "io_outA_data"} : !firrtl.uint<16>
  %io_outA_flag_4 = firrtl.wire {name = "io_outA_flag"} : !firrtl.uint<1>
  %io_outB_data_5 = firrtl.wire {name = "io_outB_data"} : !firrtl.uint<16>
  %io_outB_flag_6 = firrtl.wire {name = "io_outB_flag"} : !firrtl.uint<1>
  firrtl.strictconnect %io_in_data_0, %io_in_data : !firrtl.uint<16>
  firrtl.strictconnect %io_in_flag_1, %io_in_flag : !firrtl.uint<1>
  firrtl.strictconnect %io_inAddr_2, %io_inAddr : !firrtl.uint<8>
  firrtl.strictconnect %io_outA_data, %io_outA_data_3 : !firrtl.uint<16>
  firrtl.strictconnect %io_outA_flag, %io_outA_flag_4 : !firrtl.uint<1>
  firrtl.strictconnect %io_outB_data, %io_outB_data_5 : !firrtl.uint<16>
  firrtl.strictconnect %io_outB_flag, %io_outB_flag_6 : !firrtl.uint<1>
  %router_clock, %router_reset, %router_io_inPort_0_address, %router_io_inPort_0_data_data, %router_io_inPort_0_data_flag, %router_io_inPort_1_address, %router_io_inPort_1_data_data, %router_io_inPort_1_data_flag, %router_io_outPort_0_address, %router_io_outPort_0_data_data, %router_io_outPort_0_data_flag, %router_io_outPort_1_address, %router_io_outPort_1_data_data, %router_io_outPort_1_data_flag = firrtl.instance router @NocRouter2(in clock: !firrtl.clock, in reset: !firrtl.uint<1>, in io_inPort_0_address: !firrtl.uint<8>, in io_inPort_0_data_data: !firrtl.uint<16>, in io_inPort_0_data_flag: !firrtl.uint<1>, in io_inPort_1_address: !firrtl.uint<8>, in io_inPort_1_data_data: !firrtl.uint<16>, in io_inPort_1_data_flag: !firrtl.uint<1>, out io_outPort_0_address: !firrtl.uint<8>, out io_outPort_0_data_data: !firrtl.uint<16>, out io_outPort_0_data_flag: !firrtl.uint<1>, out io_outPort_1_address: !firrtl.uint<8>, out io_outPort_1_data_data: !firrtl.uint<16>, out io_outPort_1_data_flag: !firrtl.uint<1>)
  %router.io_inPort_0_address = firrtl.wire : !firrtl.uint<8>
  %router.io_inPort_0_data_data = firrtl.wire : !firrtl.uint<16>
  %router.io_inPort_0_data_flag = firrtl.wire : !firrtl.uint<1>
  %router.io_inPort_1_address = firrtl.wire : !firrtl.uint<8>
  %router.io_inPort_1_data_data = firrtl.wire : !firrtl.uint<16>
  %router.io_inPort_1_data_flag = firrtl.wire : !firrtl.uint<1>
  %router.io_outPort_0_address = firrtl.wire : !firrtl.uint<8>
  %router.io_outPort_0_data_data = firrtl.wire : !firrtl.uint<16>
  %router.io_outPort_0_data_flag = firrtl.wire : !firrtl.uint<1>
  %router.io_outPort_1_address = firrtl.wire : !firrtl.uint<8>
  %router.io_outPort_1_data_data = firrtl.wire : !firrtl.uint<16>
  %router.io_outPort_1_data_flag = firrtl.wire : !firrtl.uint<1>
  firrtl.strictconnect %router_io_inPort_0_address, %router.io_inPort_0_address : !firrtl.uint<8>
  firrtl.strictconnect %router_io_inPort_0_data_data, %router.io_inPort_0_data_data : !firrtl.uint<16>
  firrtl.strictconnect %router_io_inPort_0_data_flag, %router.io_inPort_0_data_flag : !firrtl.uint<1>
  firrtl.strictconnect %router_io_inPort_1_address, %router.io_inPort_1_address : !firrtl.uint<8>
  firrtl.strictconnect %router_io_inPort_1_data_data, %router.io_inPort_1_data_data : !firrtl.uint<16>
  firrtl.strictconnect %router_io_inPort_1_data_flag, %router.io_inPort_1_data_flag : !firrtl.uint<1>
  firrtl.strictconnect %router.io_outPort_0_address, %router_io_outPort_0_address : !firrtl.uint<8>
  firrtl.strictconnect %router.io_outPort_0_data_data, %router_io_outPort_0_data_data : !firrtl.uint<16>
  firrtl.strictconnect %router.io_outPort_0_data_flag, %router_io_outPort_0_data_flag : !firrtl.uint<1>
  firrtl.strictconnect %router.io_outPort_1_address, %router_io_outPort_1_address : !firrtl.uint<8>
  firrtl.strictconnect %router.io_outPort_1_data_data, %router_io_outPort_1_data_data : !firrtl.uint<16>
  firrtl.strictconnect %router.io_outPort_1_data_flag, %router_io_outPort_1_data_flag : !firrtl.uint<1>
  firrtl.strictconnect %router_clock, %clock : !firrtl.clock
  firrtl.strictconnect %router_reset, %reset : !firrtl.uint<1>
  firrtl.strictconnect %router.io_inPort_0_data_flag, %io_in_flag_1 : !firrtl.uint<1>
  firrtl.strictconnect %router.io_inPort_0_data_data, %io_in_data_0 : !firrtl.uint<16>
  firrtl.strictconnect %router.io_inPort_0_address, %io_inAddr_2 : !firrtl.uint<8>
  firrtl.strictconnect %router.io_inPort_1_data_flag, %io_in_flag_1 : !firrtl.uint<1>
  firrtl.strictconnect %router.io_inPort_1_data_data, %io_in_data_0 : !firrtl.uint<16>
  %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
  %0 = firrtl.add %io_inAddr_2, %c3_ui2 : (!firrtl.uint<8>, !firrtl.uint<2>) -> !firrtl.uint<9>
  %_router_io_inPort_1_address_T = firrtl.node %0 : !firrtl.uint<9>
  %1 = firrtl.tail %_router_io_inPort_1_address_T, 1 : (!firrtl.uint<9>) -> !firrtl.uint<8>
  %_router_io_inPort_1_address_T_1 = firrtl.node %1 : !firrtl.uint<8>
  firrtl.strictconnect %router.io_inPort_1_address, %_router_io_inPort_1_address_T_1 : !firrtl.uint<8>
  firrtl.strictconnect %io_outA_data_3, %router.io_outPort_0_data_data : !firrtl.uint<16>
  firrtl.strictconnect %io_outA_flag_4, %router.io_outPort_0_data_flag : !firrtl.uint<1>
  firrtl.strictconnect %io_outB_data_5, %router.io_outPort_1_data_data : !firrtl.uint<16>
  firrtl.strictconnect %io_outB_flag_6, %router.io_outPort_1_data_flag : !firrtl.uint<1>
}

