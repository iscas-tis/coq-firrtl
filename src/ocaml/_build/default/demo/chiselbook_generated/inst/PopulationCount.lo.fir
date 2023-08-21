circuit PopulationCount :
  module PopCountFSM :
    input clock : Clock
    input reset1 : UInt<1>
    input io_dinValid : UInt<1>
    output io_dinReady : UInt<1>
    output io_popCntValid : UInt<1>
    input io_popCntReady : UInt<1>
    output io_load : UInt<1>
    input io_done : UInt<1>

    reg stateReg : UInt<2>, clock with :
      reset => (UInt<1>("h0"), stateReg) @[PopulationCount.scala 19:25]
    node _T = asUInt(UInt<1>("h0")) @[PopulationCount.scala 24:20]
    node _T_1 = asUInt(stateReg) @[PopulationCount.scala 24:20]
    node _T_2 = eq(_T, _T_1) @[PopulationCount.scala 24:20]
    node _GEN_0 = mux(io_dinValid, UInt<1>("h1"), UInt<1>("h0")) @[PopulationCount.scala 20:11 27:25 28:17]
    node _GEN_1 = mux(io_dinValid, UInt<1>("h1"), stateReg) @[PopulationCount.scala 27:25 29:18 19:25]
    node _T_3 = asUInt(UInt<1>("h1")) @[PopulationCount.scala 24:20]
    node _T_4 = asUInt(stateReg) @[PopulationCount.scala 24:20]
    node _T_5 = eq(_T_3, _T_4) @[PopulationCount.scala 24:20]
    node _GEN_2 = mux(io_done, UInt<2>("h2"), stateReg) @[PopulationCount.scala 33:21 34:18 19:25]
    node _T_6 = asUInt(UInt<2>("h2")) @[PopulationCount.scala 24:20]
    node _T_7 = asUInt(stateReg) @[PopulationCount.scala 24:20]
    node _T_8 = eq(_T_6, _T_7) @[PopulationCount.scala 24:20]
    node _GEN_3 = mux(io_popCntReady, UInt<1>("h0"), stateReg) @[PopulationCount.scala 39:28 40:18 19:25]
    node _GEN_4 = mux(_T_8, UInt<1>("h1"), UInt<1>("h0")) @[PopulationCount.scala 22:18 24:20 38:22]
    node _GEN_5 = mux(_T_8, _GEN_3, stateReg) @[PopulationCount.scala 24:20 19:25]
    node _GEN_6 = mux(_T_5, _GEN_2, _GEN_5) @[PopulationCount.scala 24:20]
    node _GEN_7 = mux(_T_5, UInt<1>("h0"), _GEN_4) @[PopulationCount.scala 22:18 24:20]
    node _GEN_8 = mux(_T_2, UInt<1>("h1"), UInt<1>("h0")) @[PopulationCount.scala 21:15 24:20 26:19]
    node _GEN_9 = mux(_T_2, _GEN_0, UInt<1>("h0")) @[PopulationCount.scala 20:11 24:20]
    node _GEN_10 = mux(_T_2, _GEN_1, _GEN_6) @[PopulationCount.scala 24:20]
    node _GEN_11 = mux(_T_2, UInt<1>("h0"), _GEN_7) @[PopulationCount.scala 22:18 24:20]
    io_dinReady <= _GEN_8
    io_popCntValid <= _GEN_11
    io_load <= _GEN_9
    stateReg <= mux(reset1, UInt<1>("h0"), _GEN_10) @[PopulationCount.scala 19:{25,25}]

  module PopCountDataPath :
    input clock : Clock
    input reset1 : UInt<1>
    input io_din : UInt<8>
    input io_load : UInt<1>
    output io_popCnt : UInt<4>
    output io_done : UInt<1>

    reg dataReg : UInt<8>, clock with :
      reset => (UInt<1>("h0"), dataReg) @[PopulationCount.scala 54:24]
    reg popCntReg : UInt<8>, clock with :
      reset => (UInt<1>("h0"), popCntReg) @[PopulationCount.scala 55:26]
    reg counterReg : UInt<4>, clock with :
      reset => (UInt<1>("h0"), counterReg) @[PopulationCount.scala 56:26]
    node _dataReg_T = bits(dataReg, 7, 1) @[PopulationCount.scala 58:28]
    node _dataReg_T_1 = cat(UInt<1>("h0"), _dataReg_T) @[PopulationCount.scala 58:18]
    node _popCntReg_T = bits(dataReg, 0, 0) @[PopulationCount.scala 59:35]
    node _popCntReg_T_1 = add(popCntReg, _popCntReg_T) @[PopulationCount.scala 59:26]
    node _popCntReg_T_2 = tail(_popCntReg_T_1, 1) @[PopulationCount.scala 59:26]
    node done = eq(counterReg, UInt<1>("h0")) @[PopulationCount.scala 61:25]
    node _T = eq(done, UInt<1>("h0")) @[PopulationCount.scala 62:9]
    node _counterReg_T = sub(counterReg, UInt<1>("h1")) @[PopulationCount.scala 63:30]
    node _counterReg_T_1 = tail(_counterReg_T, 1) @[PopulationCount.scala 63:30]
    node _GEN_0 = mux(_T, _counterReg_T_1, counterReg) @[PopulationCount.scala 62:16 63:16 56:26]
    node _GEN_1 = mux(io_load, io_din, _dataReg_T_1) @[PopulationCount.scala 58:11 66:17 67:13]
    node _GEN_2 = mux(io_load, UInt<1>("h0"), _popCntReg_T_2) @[PopulationCount.scala 59:13 66:17 68:15]
    node _GEN_3 = mux(io_load, UInt<4>("h8"), _GEN_0) @[PopulationCount.scala 66:17 69:16]
    node _T_1 = asUInt(reset1) @[PopulationCount.scala 73:9]
    node _T_2 = eq(_T_1, UInt<1>("h0")) @[PopulationCount.scala 73:9]
    io_popCnt <= bits(popCntReg, 3, 0) @[PopulationCount.scala 75:13]
    io_done <= done @[PopulationCount.scala 76:11]
    dataReg <= mux(reset1, UInt<8>("h0"), _GEN_1) @[PopulationCount.scala 54:{24,24}]
    popCntReg <= mux(reset1, UInt<8>("h0"), _GEN_2) @[PopulationCount.scala 55:{26,26}]
    counterReg <= mux(reset1, UInt<4>("h0"), _GEN_3) @[PopulationCount.scala 56:{26,26}]

  module PopulationCount :
    input clock : Clock
    input reset1 : UInt<1>
    input io_dinValid : UInt<1>
    output io_dinReady : UInt<1>
    input io_din : UInt<8>
    output io_popCntValid : UInt<1>
    input io_popCntReady : UInt<1>
    output io_popCnt : UInt<4>

    inst fsm aof PopCountFSM @[PopulationCount.scala 92:19]
    inst data aof PopCountDataPath @[PopulationCount.scala 93:20]
    io_dinReady <= fsm.io_dinReady @[PopulationCount.scala 96:15]
    io_popCntValid <= fsm.io_popCntValid @[PopulationCount.scala 97:18]
    io_popCnt <= data.io_popCnt @[PopulationCount.scala 101:13]
    fsm.clock <= clock
    fsm.reset1 <= reset1
    fsm.io_dinValid <= io_dinValid @[PopulationCount.scala 95:19]
    fsm.io_popCntReady <= io_popCntReady @[PopulationCount.scala 98:22]
    fsm.io_done <= data.io_done @[PopulationCount.scala 103:15]
    data.clock <= clock
    data.reset1 <= reset1
    data.io_din <= io_din @[PopulationCount.scala 100:15]
    data.io_load <= fsm.io_load @[PopulationCount.scala 102:16]
