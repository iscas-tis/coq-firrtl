circuit Comparator :
  module Comparator :
    input clock : Clock
    input reset1 : UInt<1>
    input io_a : UInt<8>
    input io_b : UInt<8>
    output io_equ : UInt<1>
    output io_gt : UInt<1>

    node equ = eq(io_a, io_b) @[Comparator.scala 15:15]
    node gt1 = gt(io_a, io_b) @[Comparator.scala 16:14]
    io_equ <= equ @[Comparator.scala 18:10]
    io_gt <= gt1 @[Comparator.scala 19:9]
