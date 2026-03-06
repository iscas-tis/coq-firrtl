circuit RisingMooreFsm :
  module RisingMooreFsm :
    input clock : Clock
    input reset1 : UInt<1>
    input io_din : UInt<1>
    output io_risingEdge : UInt<1>

    reg stateReg : UInt<2>, clock with :
      reset => (UInt<1>("h0"), stateReg) @[RisingMooreFsm.scala 17:25]
    node _T = asUInt(UInt<1>("h0")) @[RisingMooreFsm.scala 20:21]
    node _T_1 = asUInt(stateReg) @[RisingMooreFsm.scala 20:21]
    node _T_2 = eq(_T, _T_1) @[RisingMooreFsm.scala 20:21]
    node _GEN_0 = mux(io_din, UInt<1>("h1"), stateReg) @[RisingMooreFsm.scala 22:20 23:18 17:25]
    node _T_3 = asUInt(UInt<1>("h1")) @[RisingMooreFsm.scala 20:21]
    node _T_4 = asUInt(stateReg) @[RisingMooreFsm.scala 20:21]
    node _T_5 = eq(_T_3, _T_4) @[RisingMooreFsm.scala 20:21]
    node _GEN_1 = mux(io_din, UInt<2>("h2"), UInt<1>("h0")) @[RisingMooreFsm.scala 27:20 28:18 30:18]
    node _T_6 = asUInt(UInt<2>("h2")) @[RisingMooreFsm.scala 20:21]
    node _T_7 = asUInt(stateReg) @[RisingMooreFsm.scala 20:21]
    node _T_8 = eq(_T_6, _T_7) @[RisingMooreFsm.scala 20:21]
    node _T_9 = eq(io_din, UInt<1>("h0")) @[RisingMooreFsm.scala 34:12]
    node _GEN_2 = mux(_T_9, UInt<1>("h0"), stateReg) @[RisingMooreFsm.scala 34:21 35:18 17:25]
    node _GEN_3 = mux(_T_8, _GEN_2, stateReg) @[RisingMooreFsm.scala 20:21 17:25]
    node _GEN_4 = mux(_T_5, _GEN_1, _GEN_3) @[RisingMooreFsm.scala 20:21]
    node _GEN_5 = mux(_T_2, _GEN_0, _GEN_4) @[RisingMooreFsm.scala 20:21]
    node _io_risingEdge_T = eq(stateReg, UInt<1>("h1")) @[RisingMooreFsm.scala 41:29]
    io_risingEdge <= _io_risingEdge_T @[RisingMooreFsm.scala 41:17]
    stateReg <= mux(reset1, UInt<1>("h0"), _GEN_5) @[RisingMooreFsm.scala 17:{25,25}]
