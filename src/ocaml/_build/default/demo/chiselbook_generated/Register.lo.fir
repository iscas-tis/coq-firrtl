circuit Register :
  module Register :
    input clock : Clock
    input reset1 : UInt<1>
    input io_d : UInt<8>
    output io_q : UInt<8>

    reg reg1 : UInt<8>, clock with :
      reset => (UInt<1>("h0"), reg1) @[components.scala 35:20]
    io_q <= reg1 @[components.scala 37:8]
    reg1 <= mux(reset1, UInt<1>("h0"), io_d) @[components.scala 35:{20,20} 36:7]
