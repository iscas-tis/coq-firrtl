circuit Formal :
  module FormalSimple :
    input clock : Clock
    input reset : Reset
    output io : { flip a : UInt<32>, flip b : UInt<32>, y : UInt<32>}

    node _io_y_T = and(io.a, io.b) @[formal.scala 10:16]
    io.y <= _io_y_T @[formal.scala 10:8]

  module Formal :
    input clock : Clock
    input reset : UInt<1>
    output io : { flip a : UInt<32>, flip b : UInt<32>, y : UInt<32>}

    inst inst of FormalSimple @[formal.scala 19:20]
    inst.clock <= clock
    inst.reset <= reset
    inst.io.a <= io.a @[formal.scala 20:13]
    inst.io.b <= io.b @[formal.scala 21:13]
    io.y <= inst.io.y @[formal.scala 22:8]

