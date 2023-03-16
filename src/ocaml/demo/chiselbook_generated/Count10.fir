circuit Count10 :
  module Adder :
    input clock : Clock
    input reset : Reset
    output io : { flip a : UInt<8>, flip b : UInt<8>, y : UInt<8>}

    node _io_y_T = add(io.a, io.b) @[components.scala 15:16]
    node _io_y_T_1 = tail(_io_y_T, 1) @[components.scala 15:16]
    io.y <= _io_y_T_1 @[components.scala 15:8]

  module Register :
    input clock : Clock
    input reset : Reset
    output io : { flip d : UInt<8>, q : UInt<8>}

    reg reg : UInt, clock with :
      reset => (reset, UInt<1>("h0")) @[components.scala 26:20]
    reg <= io.d @[components.scala 27:7]
    io.q <= reg @[components.scala 28:8]

  module Count10 :
    input clock : Clock
    input reset : UInt<1>
    output io : { dout : UInt<8>}

    inst add of Adder @[components.scala 38:19]
    add.clock <= clock
    add.reset <= reset
    inst reg of Register @[components.scala 39:19]
    reg.clock <= clock
    reg.reset <= reset
    add.io.a <= UInt<1>("h1") @[components.scala 45:12]
    add.io.b <= reg.io.q @[components.scala 46:12]
    node _next_T = eq(reg.io.q, UInt<4>("h9")) @[components.scala 50:24]
    node next = mux(_next_T, UInt<1>("h0"), add.io.y) @[components.scala 50:17]
    reg.io.d <= next @[components.scala 51:12]
    io.dout <= reg.io.q @[components.scala 53:11]

