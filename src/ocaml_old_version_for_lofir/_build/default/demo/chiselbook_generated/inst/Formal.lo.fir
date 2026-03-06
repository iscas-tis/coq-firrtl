circuit Formal :
  module FormalSimple :
    input clock : Clock
    input reset1 : UInt<1>
    input io_a : UInt<32>
    input io_b : UInt<32>
    output io_y : UInt<32>

    node _io_y_T = and(io_a, io_b) @[formal.scala 10:16]
    io_y <= _io_y_T @[formal.scala 10:8]

  module Formal :
    input clock : Clock
    input reset1 : UInt<1>
    input io_a : UInt<32>
    input io_b : UInt<32>
    output io_y : UInt<32>

    inst inst1 aof FormalSimple @[formal.scala 19:20]
    io_y <= inst1.io_y @[formal.scala 22:8]
    inst1.clock <= clock
    inst1.reset1 <= reset1
    inst1.io_a <= io_a @[formal.scala 20:13]
    inst1.io_b <= io_b @[formal.scala 21:13]
