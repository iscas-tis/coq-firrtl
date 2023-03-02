circuit CombWhen2Untested :
  module CombWhen2Untested :
    input clock : Clock
    input reset : UInt<1>
    output io : { flip data : UInt<4>, out : UInt<1>}

    wire enoughMoney : UInt<1> @[Combinational.scala 77:25]
    enoughMoney <= UInt<1>("h0") @[Combinational.scala 79:15]
    node _T = geq(io.data, UInt<3>("h5")) @[Combinational.scala 80:17]
    when _T : @[Combinational.scala 80:27]
      enoughMoney <= UInt<1>("h1") @[Combinational.scala 81:17]
    io.out <= enoughMoney @[Combinational.scala 84:10]

