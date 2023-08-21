circuit UseParamRouter :
  module NocRouter :
    input clock : Clock
    input reset1 : UInt<1>
    input io_inPort_0_data : UInt<16>
    input io_inPort_0_flag : UInt<1>
    input io_inPort_1_data : UInt<16>
    input io_inPort_1_flag : UInt<1>
    input io_address_0 : UInt<8>
    input io_address_1 : UInt<8>
    output io_outPort_0_data : UInt<16>
    output io_outPort_0_flag : UInt<1>
    output io_outPort_1_data : UInt<16>
    output io_outPort_1_flag : UInt<1>

    io_outPort_0_data <= io_inPort_1_data @[NocRouter.scala 22:17]
    io_outPort_0_flag <= io_inPort_1_flag @[NocRouter.scala 22:17]
    io_outPort_1_data <= io_inPort_0_data @[NocRouter.scala 23:17]
    io_outPort_1_flag <= io_inPort_0_flag @[NocRouter.scala 23:17]

  module UseParamRouter :
    input clock : Clock
    input reset1 : UInt<1>
    input io_in_data : UInt<16>
    input io_in_flag : UInt<1>
    input io_inAddr : UInt<8>
    output io_outA_data : UInt<16>
    output io_outA_flag : UInt<1>
    output io_outB_data : UInt<16>
    output io_outB_flag : UInt<1>

    inst router aof NocRouter @[NocRouter.scala 35:22]
    node _router_io_address_1_T = add(io_inAddr, UInt<2>("h3")) @[NocRouter.scala 42:36]
    node _router_io_address_1_T_1 = tail(_router_io_address_1_T, 1) @[NocRouter.scala 42:36]
    io_outA_data <= router.io_outPort_0_data @[NocRouter.scala 43:11]
    io_outA_flag <= router.io_outPort_0_flag @[NocRouter.scala 43:11]
    io_outB_data <= router.io_outPort_1_data @[NocRouter.scala 44:11]
    io_outB_flag <= router.io_outPort_1_flag @[NocRouter.scala 44:11]
    router.clock <= clock
    router.reset1 <= reset1
    router.io_inPort_0_data <= io_in_data @[NocRouter.scala 39:23]
    router.io_inPort_0_flag <= io_in_flag @[NocRouter.scala 39:23]
    router.io_inPort_1_data <= io_in_data @[NocRouter.scala 41:23]
    router.io_inPort_1_flag <= io_in_flag @[NocRouter.scala 41:23]
    router.io_address_0 <= io_inAddr @[NocRouter.scala 40:24]
    router.io_address_1 <= _router_io_address_1_T_1 @[NocRouter.scala 42:24]
