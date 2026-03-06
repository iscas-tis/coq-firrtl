circuit UseParamRouter2 :
  module NocRouter2 :
    input clock : Clock
    input reset1 : UInt<1>
    input io_inPort_0_address : UInt<8>
    input io_inPort_0_data_data : UInt<16>
    input io_inPort_0_data_flag : UInt<1>
    input io_inPort_1_address : UInt<8>
    input io_inPort_1_data_data : UInt<16>
    input io_inPort_1_data_flag : UInt<1>
    output io_outPort_0_address : UInt<8>
    output io_outPort_0_data_data : UInt<16>
    output io_outPort_0_data_flag : UInt<1>
    output io_outPort_1_address : UInt<8>
    output io_outPort_1_data_data : UInt<16>
    output io_outPort_1_data_flag : UInt<1>

    io_outPort_0_address <= io_inPort_1_address @[NocRouter.scala 84:17]
    io_outPort_0_data_data <= io_inPort_1_data_data @[NocRouter.scala 84:17]
    io_outPort_0_data_flag <= io_inPort_1_data_flag @[NocRouter.scala 84:17]
    io_outPort_1_address <= io_inPort_0_address @[NocRouter.scala 85:17]
    io_outPort_1_data_data <= io_inPort_0_data_data @[NocRouter.scala 85:17]
    io_outPort_1_data_flag <= io_inPort_0_data_flag @[NocRouter.scala 85:17]

  module UseParamRouter2 :
    input clock : Clock
    input reset1 : UInt<1>
    input io_in_data : UInt<16>
    input io_in_flag : UInt<1>
    input io_inAddr : UInt<8>
    output io_outA_data : UInt<16>
    output io_outA_flag : UInt<1>
    output io_outB_data : UInt<16>
    output io_outB_flag : UInt<1>

    inst router aof NocRouter2 @[NocRouter.scala 97:22]
    node _router_io_inPort_1_address_T = add(io_inAddr, UInt<2>("h3")) @[NocRouter.scala 104:43]
    node _router_io_inPort_1_address_T_1 = tail(_router_io_inPort_1_address_T, 1) @[NocRouter.scala 104:43]
    io_outA_data <= router.io_outPort_0_data_data @[NocRouter.scala 105:11]
    io_outA_flag <= router.io_outPort_0_data_flag @[NocRouter.scala 105:11]
    io_outB_data <= router.io_outPort_1_data_data @[NocRouter.scala 106:11]
    io_outB_flag <= router.io_outPort_1_data_flag @[NocRouter.scala 106:11]
    router.clock <= clock
    router.reset1 <= reset1
    router.io_inPort_0_address <= io_inAddr @[NocRouter.scala 102:31]
    router.io_inPort_0_data_data <= io_in_data @[NocRouter.scala 101:28]
    router.io_inPort_0_data_flag <= io_in_flag @[NocRouter.scala 101:28]
    router.io_inPort_1_address <= _router_io_inPort_1_address_T_1 @[NocRouter.scala 104:31]
    router.io_inPort_1_data_data <= io_in_data @[NocRouter.scala 103:28]
    router.io_inPort_1_data_flag <= io_in_flag @[NocRouter.scala 103:28]
