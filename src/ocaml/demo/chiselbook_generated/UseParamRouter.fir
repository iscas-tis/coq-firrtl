circuit UseParamRouter :
  module NocRouter :
    input clock : Clock
    input reset : Reset
    output io : { flip inPort : { data : UInt<16>, flag : UInt<1>}[2], flip address : UInt<8>[2], outPort : { data : UInt<16>, flag : UInt<1>}[2]}

    io.outPort[0] <= io.inPort[1] @[NocRouter.scala 22:17]
    io.outPort[1] <= io.inPort[0] @[NocRouter.scala 23:17]

  module UseParamRouter :
    input clock : Clock
    input reset : UInt<1>
    output io : { flip in : { data : UInt<16>, flag : UInt<1>}, flip inAddr : UInt<8>, outA : { data : UInt<16>, flag : UInt<1>}, outB : { data : UInt<16>, flag : UInt<1>}}

    inst router of NocRouter @[NocRouter.scala 35:22]
    router.clock <= clock
    router.reset <= reset
    router.io.inPort[0].flag <= io.in.flag @[NocRouter.scala 39:23]
    router.io.inPort[0].data <= io.in.data @[NocRouter.scala 39:23]
    router.io.address[0] <= io.inAddr @[NocRouter.scala 40:24]
    router.io.inPort[1].flag <= io.in.flag @[NocRouter.scala 41:23]
    router.io.inPort[1].data <= io.in.data @[NocRouter.scala 41:23]
    node _router_io_address_1_T = add(io.inAddr, UInt<2>("h3")) @[NocRouter.scala 42:36]
    node _router_io_address_1_T_1 = tail(_router_io_address_1_T, 1) @[NocRouter.scala 42:36]
    router.io.address[1] <= _router_io_address_1_T_1 @[NocRouter.scala 42:24]
    io.outA <= router.io.outPort[0] @[NocRouter.scala 43:11]
    io.outB <= router.io.outPort[1] @[NocRouter.scala 44:11]

