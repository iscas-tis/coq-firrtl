circuit RisingFsm :
  module RisingFsm :
    input clock : Clock
    input reset1 : UInt<1>
    input io_din : UInt<1>
    output io_risingEdge : UInt<1>

    reg stateReg : UInt<1>, clock with :
      reset => (UInt<1>("h0"), stateReg) @[RisingFsm.scala 18:25]
    node _T = asUInt(UInt<1>("h0")) @[RisingFsm.scala 24:21]
    node _T_1 = asUInt(stateReg) @[RisingFsm.scala 24:21]
    node _T_2 = eq(_T, _T_1) @[RisingFsm.scala 24:21]
    node _GEN_0 = mux(io_din, UInt<1>("h1"), stateReg) @[RisingFsm.scala 26:20 27:18 18:25]
    node _GEN_1 = mux(io_din, UInt<1>("h1"), UInt<1>("h0")) @[RisingFsm.scala 21:17 26:20 28:23]
    node _T_3 = asUInt(UInt<1>("h1")) @[RisingFsm.scala 24:21]
    node _T_4 = asUInt(stateReg) @[RisingFsm.scala 24:21]
    node _T_5 = eq(_T_3, _T_4) @[RisingFsm.scala 24:21]
    node _T_6 = eq(io_din, UInt<1>("h0")) @[RisingFsm.scala 32:12]
    node _GEN_2 = mux(_T_6, UInt<1>("h0"), stateReg) @[RisingFsm.scala 32:21 33:18 18:25]
    node _GEN_3 = mux(_T_5, _GEN_2, stateReg) @[RisingFsm.scala 24:21 18:25]
    node _GEN_4 = mux(_T_2, _GEN_0, _GEN_3) @[RisingFsm.scala 24:21]
    node _GEN_5 = mux(_T_2, _GEN_1, UInt<1>("h0")) @[RisingFsm.scala 21:17 24:21]
    io_risingEdge <= _GEN_5
    stateReg <= mux(reset1, UInt<1>("h0"), _GEN_4) @[RisingFsm.scala 18:{25,25}]
