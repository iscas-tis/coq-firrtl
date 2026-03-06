circuit CombWhen2Untested :
  module CombWhen2Untested :
    input clock : Clock
    input reset1 : UInt<1>
    input io_data : UInt<4>
    output io_out : UInt<1>

    node _T = geq(io_data, UInt<3>("h5")) @[Combinational.scala 80:17]
    node _GEN_0 = mux(_T, UInt<1>("h1"), UInt<1>("h0")) @[Combinational.scala 79:15 80:27 81:17]
    node enoughMoney = _GEN_0 @[Combinational.scala 77:25]
    io_out <= enoughMoney @[Combinational.scala 84:10]
