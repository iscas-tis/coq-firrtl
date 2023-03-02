circuit CombElseWhen :
  module CombElseWhen :
    input clock : Clock
    input reset : UInt<1>
    output io : { flip cond : UInt<1>, flip cond2 : UInt<1>, out : UInt<4>}

    wire w : UInt @[Combinational.scala 133:15]
    when io.cond : @[Combinational.scala 135:15]
      w <= UInt<1>("h1") @[Combinational.scala 136:7]
    else :
      when io.cond2 : @[Combinational.scala 137:23]
        w <= UInt<2>("h2") @[Combinational.scala 138:7]
      else :
        w <= UInt<2>("h3") @[Combinational.scala 140:7]
    io.out <= w @[Combinational.scala 143:10]

