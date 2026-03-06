circuit Count10 :
  module Adder :
    input clock : Clock
    input reset1 : UInt<1>
    input io_a : UInt<8>
    input io_b : UInt<8>
    output io_y : UInt<8>

    node _io_y_T = add(io_a, io_b) @[components.scala 15:16]
    node _io_y_T_1 = tail(_io_y_T, 1) @[components.scala 15:16]
    io_y <= _io_y_T_1 @[components.scala 15:8]

  module Register :
    input clock : Clock
    input reset1 : UInt<1>
    input io_d : UInt<8>
    output io_q : UInt<8>

    reg reg1 : UInt<8>, clock with :
      reset => (UInt<1>("h0"), reg1) @[components.scala 26:20]
    io_q <= reg1 @[components.scala 28:8]
    reg1 <= mux(reset1, UInt<1>("h0"), io_d) @[components.scala 26:{20,20} 27:7]

  module Count10 :
    input clock : Clock
    input reset1 : UInt<1>
    output io_dout : UInt<8>

    inst add1 aof Adder @[components.scala 38:19]
    inst reg1 aof Register @[components.scala 39:19]
    node _next_T = eq(reg1.io_q, UInt<4>("h9")) @[components.scala 50:24]
    node next = mux(_next_T, UInt<1>("h0"), add1.io_y) @[components.scala 50:17]
    io_dout <= reg1.io_q @[components.scala 53:11]
    add1.clock <= clock
    add1.reset1 <= reset1
    add1.io_a <= UInt<8>("h1") @[components.scala 45:12]
    add1.io_b <= reg1.io_q @[components.scala 46:12]
    reg1.clock <= clock
    reg1.reset1 <= reset1
    reg1.io_d <= next @[components.scala 51:12]
