circuit FunctionCounter :
  module FunctionCounter :
    input clock : Clock
    input reset1 : UInt<1>
    output io_cnt : UInt<8>
    output io_tick : UInt<1>

    reg count10 : UInt<8>, clock with :
      reset => (UInt<1>("h0"), count10) @[Counter.scala 114:25]
    node _count10_cntReg_T = eq(count10, UInt<4>("ha")) @[Counter.scala 115:26]
    node _count10_cntReg_T_1 = add(count10, UInt<1>("h1")) @[Counter.scala 115:47]
    node _count10_cntReg_T_2 = tail(_count10_cntReg_T_1, 1) @[Counter.scala 115:47]
    node _count10_cntReg_T_3 = mux(_count10_cntReg_T, UInt<1>("h0"), _count10_cntReg_T_2) @[Counter.scala 115:18]
    reg count99 : UInt<8>, clock with :
      reset => (UInt<1>("h0"), count99) @[Counter.scala 114:25]
    node _count99_cntReg_T = eq(count99, UInt<7>("h63")) @[Counter.scala 115:26]
    node _count99_cntReg_T_1 = add(count99, UInt<1>("h1")) @[Counter.scala 115:47]
    node _count99_cntReg_T_2 = tail(_count99_cntReg_T_1, 1) @[Counter.scala 115:47]
    node _count99_cntReg_T_3 = mux(_count99_cntReg_T, UInt<1>("h0"), _count99_cntReg_T_2) @[Counter.scala 115:18]
    reg testCounter : UInt<8>, clock with :
      reset => (UInt<1>("h0"), testCounter) @[Counter.scala 114:25]
    node _testCounter_cntReg_T = eq(testCounter, UInt<3>("h7")) @[Counter.scala 115:26]
    node _testCounter_cntReg_T_1 = add(testCounter, UInt<1>("h1")) @[Counter.scala 115:47]
    node _testCounter_cntReg_T_2 = tail(_testCounter_cntReg_T_1, 1) @[Counter.scala 115:47]
    node _testCounter_cntReg_T_3 = mux(_testCounter_cntReg_T, UInt<1>("h0"), _testCounter_cntReg_T_2) @[Counter.scala 115:18]
    node _io_tick_T = eq(testCounter, UInt<3>("h7")) @[Counter.scala 126:26]
    io_cnt <= testCounter @[Counter.scala 127:10]
    io_tick <= _io_tick_T @[Counter.scala 126:11]
    count10 <= mux(reset1, UInt<8>("h0"), _count10_cntReg_T_3) @[Counter.scala 114:{25,25} 115:12]
    count99 <= mux(reset1, UInt<8>("h0"), _count99_cntReg_T_3) @[Counter.scala 114:{25,25} 115:12]
    testCounter <= mux(reset1, UInt<8>("h0"), _testCounter_cntReg_T_3) @[Counter.scala 114:{25,25} 115:12]
