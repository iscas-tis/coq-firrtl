circuit Conditional :
  module Conditional :
    input clock : Clock
    input reset : UInt<1>
    output io : { flip condition : UInt<1>, result : UInt<4>}

    node c1 = eq(io.condition, UInt<1>("h0")) @[Snippets.scala 91:12]
    node c2 = eq(io.condition, UInt<1>("h0")) @[Snippets.scala 92:12]
    wire v : UInt @[Snippets.scala 94:15]
    v <= UInt<3>("h5") @[Snippets.scala 96:5]
    when io.condition : @[Snippets.scala 97:20]
      v <= UInt<1>("h0") @[Snippets.scala 98:7]
    when c1 : @[Snippets.scala 101:13]
      v <= UInt<1>("h1") @[Snippets.scala 101:17]
    when c2 : @[Snippets.scala 102:13]
      v <= UInt<2>("h2") @[Snippets.scala 102:17]
    when c1 : @[Snippets.scala 104:13]
      v <= UInt<1>("h1") @[Snippets.scala 104:17]
    else :
      when c2 : @[Snippets.scala 105:20]
        v <= UInt<2>("h2") @[Snippets.scala 105:24]
      else :
        v <= UInt<2>("h3") @[Snippets.scala 106:20]
    io.result <= v @[Snippets.scala 108:13]

