circuit Hello :
  module Hello :
    input clock : Clock
    input reset1 : UInt<1>
    output io_led : UInt<1>

    reg cntReg : UInt<32>, clock with :
      reset => (UInt<1>("h0"), cntReg) @[Hello.scala 26:23]
    reg blkReg : UInt<1>, clock with :
      reset => (UInt<1>("h0"), blkReg) @[Hello.scala 27:23]
    node _cntReg_T = add(cntReg, UInt<1>("h1")) @[Hello.scala 29:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Hello.scala 29:20]
    node _T = eq(cntReg, UInt<25>("h17d783f")) @[Hello.scala 30:15]
    node _blkReg_T = not(blkReg) @[Hello.scala 32:15]
    node _GEN_0 = mux(_T, UInt<1>("h0"), _cntReg_T_1) @[Hello.scala 29:10 30:28 31:12]
    node _GEN_1 = mux(_T, _blkReg_T, blkReg) @[Hello.scala 30:28 32:12 27:23]
    io_led <= blkReg @[Hello.scala 34:10]
    cntReg <= mux(reset1, UInt<32>("h0"), _GEN_0) @[Hello.scala 26:{23,23}]
    blkReg <= mux(reset1, UInt<1>("h0"), _GEN_1) @[Hello.scala 27:{23,23}]
