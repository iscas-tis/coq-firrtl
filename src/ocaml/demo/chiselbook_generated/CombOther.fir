circuit CombOther :
  module CombOther :
    input clock : Clock
    input reset : UInt<1>
    output io : { flip cond : UInt<1>, out : UInt<4>}

    wire w : UInt @[Combinational.scala 103:15]
    when io.cond : @[Combinational.scala 105:15]
      w <= UInt<1>("h1") @[Combinational.scala 106:7]
    else :
      w <= UInt<2>("h2") @[Combinational.scala 108:7]
    io.out <= w @[Combinational.scala 111:10]

