circuit DebounceFunc :
  module DebounceFunc :
    input clock : Clock
    input reset1 : UInt<1>
    input io_btnU : UInt<1>
    output io_led : UInt<8>

    reg btnSync_REG : UInt<1>, clock with :
      reset => (UInt<1>("h0"), btnSync_REG) @[Debounce.scala 76:38]
    reg btnSync : UInt<1>, clock with :
      reset => (UInt<1>("h0"), btnSync) @[Debounce.scala 76:30]
    reg tick_reg : UInt<20>, clock with :
      reset => (UInt<1>("h0"), tick_reg) @[Debounce.scala 81:22]
    node tick = eq(tick_reg, UInt<20>("hf423f")) @[Debounce.scala 82:20]
    node _tick_reg_T = add(tick_reg, UInt<1>("h1")) @[Debounce.scala 83:31]
    node _tick_reg_T_1 = tail(_tick_reg_T, 1) @[Debounce.scala 83:31]
    node _tick_reg_T_2 = mux(tick, UInt<1>("h0"), _tick_reg_T_1) @[Debounce.scala 83:15]
    reg btnDeb : UInt<1>, clock with :
      reset => (UInt<1>("h0"), btnDeb) @[Debounce.scala 98:19]
    node _GEN_0 = mux(tick, btnSync, btnDeb) @[Debounce.scala 100:12 99:15 98:19]
    reg btnClean_reg : UInt<3>, clock with :
      reset => (UInt<1>("h0"), btnClean_reg) @[Debounce.scala 88:22]
    node _btnClean_reg_T = bits(btnClean_reg, 1, 0) @[Debounce.scala 90:17]
    node _btnClean_reg_T_1 = cat(_btnClean_reg_T, btnDeb) @[Debounce.scala 90:24]
    node _GEN_1 = mux(tick, _btnClean_reg_T_1, btnClean_reg) @[Debounce.scala 89:14 90:11 88:22]
    node _btnClean_T = bits(btnClean_reg, 2, 2) @[Debounce.scala 92:9]
    node _btnClean_T_1 = bits(btnClean_reg, 1, 1) @[Debounce.scala 92:18]
    node _btnClean_T_2 = and(_btnClean_T, _btnClean_T_1) @[Debounce.scala 92:13]
    node _btnClean_T_3 = bits(btnClean_reg, 2, 2) @[Debounce.scala 92:29]
    node _btnClean_T_4 = bits(btnClean_reg, 0, 0) @[Debounce.scala 92:38]
    node _btnClean_T_5 = and(_btnClean_T_3, _btnClean_T_4) @[Debounce.scala 92:33]
    node _btnClean_T_6 = or(_btnClean_T_2, _btnClean_T_5) @[Debounce.scala 92:23]
    node _btnClean_T_7 = bits(btnClean_reg, 1, 1) @[Debounce.scala 92:49]
    node _btnClean_T_8 = bits(btnClean_reg, 0, 0) @[Debounce.scala 92:58]
    node _btnClean_T_9 = and(_btnClean_T_7, _btnClean_T_8) @[Debounce.scala 92:53]
    node btnClean = or(_btnClean_T_6, _btnClean_T_9) @[Debounce.scala 92:43]
    reg risingEdge_REG : UInt<1>, clock with :
      reset => (UInt<1>("h0"), risingEdge_REG) @[Debounce.scala 78:37]
    node _risingEdge_T = eq(risingEdge_REG, UInt<1>("h0")) @[Debounce.scala 78:29]
    node risingEdge = and(btnClean, _risingEdge_T) @[Debounce.scala 78:27]
    reg reg1 : UInt<8>, clock with :
      reset => (UInt<1>("h0"), reg1) @[Debounce.scala 108:20]
    node _reg_T = add(reg1, UInt<1>("h1")) @[Debounce.scala 110:16]
    node _reg_T_1 = tail(_reg_T, 1) @[Debounce.scala 110:16]
    node _GEN_2 = mux(risingEdge, _reg_T_1, reg1) @[Debounce.scala 108:20 109:21 110:9]
    io_led <= reg1 @[Debounce.scala 113:10]
    btnSync_REG <= io_btnU @[Debounce.scala 76:38]
    btnSync <= btnSync_REG @[Debounce.scala 76:30]
    tick_reg <= mux(reset1, UInt<20>("h0"), _tick_reg_T_2) @[Debounce.scala 81:{22,22} 83:9]
    btnDeb <= _GEN_0
    btnClean_reg <= mux(reset1, UInt<3>("h0"), _GEN_1) @[Debounce.scala 88:{22,22}]
    risingEdge_REG <= btnClean @[Debounce.scala 78:37]
    reg1 <= mux(reset1, UInt<8>("h0"), _GEN_2) @[Debounce.scala 108:{20,20}]
