circuit UseParamRouter2 :
  module NocRouter2 :
    input clock : Clock
    input reset : Reset
    output io : { flip inPort : { address : UInt<8>, data : { data : UInt<16>, flag : UInt<1>}}[2], outPort : { address : UInt<8>, data : { data : UInt<16>, flag : UInt<1>}}[2]}

    io.outPort[0] <= io.inPort[1] @[NocRouter.scala 84:17]
    io.outPort[1] <= io.inPort[0] @[NocRouter.scala 85:17]

  module UseParamRouter2 :
    input clock : Clock
    input reset : UInt<1>
    output io : { flip in : { data : UInt<16>, flag : UInt<1>}, flip inAddr : UInt<8>, outA : { data : UInt<16>, flag : UInt<1>}, outB : { data : UInt<16>, flag : UInt<1>}}

    inst router of NocRouter2 @[NocRouter.scala 97:22]
    router.clock <= clock
    router.reset <= reset
    router.io.inPort[0].data.flag <= io.in.flag @[NocRouter.scala 101:28]
    router.io.inPort[0].data.data <= io.in.data @[NocRouter.scala 101:28]
    router.io.inPort[0].address <= io.inAddr @[NocRouter.scala 102:31]
    router.io.inPort[1].data.flag <= io.in.flag @[NocRouter.scala 103:28]
    router.io.inPort[1].data.data <= io.in.data @[NocRouter.scala 103:28]
    node _router_io_inPort_1_address_T = add(io.inAddr, UInt<2>("h3")) @[NocRouter.scala 104:43]
    node _router_io_inPort_1_address_T_1 = tail(_router_io_inPort_1_address_T, 1) @[NocRouter.scala 104:43]
    router.io.inPort[1].address <= _router_io_inPort_1_address_T_1 @[NocRouter.scala 104:31]
    io.outA <= router.io.outPort[0].data @[NocRouter.scala 105:11]
    io.outB <= router.io.outPort[1].data @[NocRouter.scala 106:11]

