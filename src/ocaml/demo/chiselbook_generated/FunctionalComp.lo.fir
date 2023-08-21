circuit FunctionalComp :
  module FunctionalComp :
    input clock : Clock
    input reset1 : UInt<1>
    input io_a : UInt<8>
    input io_b : UInt<8>
    output io_equ : UInt<8>
    output io_gt : UInt<8>

    node equResult = eq(io_a, io_b) @[functional.scala 57:17]
    node gtResult = gt(io_a, io_b) @[functional.scala 58:16]
    node equ = eq(io_a, io_b) @[functional.scala 57:17]
    node gt1 = gt(io_a, io_b) @[functional.scala 58:16]
    io_equ <= pad(equ, 8) @[functional.scala 76:10]
    io_gt <= pad(gt1, 8) @[functional.scala 77:9]
