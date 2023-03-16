circuit FunctionalComp :
  module FunctionalComp :
    input clock : Clock
    input reset : UInt<1>
    output io : { flip a : UInt<8>, flip b : UInt<8>, equ : UInt<8>, gt : UInt<8>}

    node equResult = eq(io.a, io.b) @[functional.scala 57:17]
    node gtResult = gt(io.a, io.b) @[functional.scala 58:16]
    node equ = eq(io.a, io.b) @[functional.scala 57:17]
    node gt = gt(io.a, io.b) @[functional.scala 58:16]
    io.equ <= equResult @[functional.scala 73:10]
    io.gt <= gtResult @[functional.scala 74:9]
    io.equ <= equ @[functional.scala 76:10]
    io.gt <= gt @[functional.scala 77:9]

