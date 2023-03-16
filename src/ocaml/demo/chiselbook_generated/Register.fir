circuit Register :
  module Register :
    input clock : Clock
    input reset : UInt<1>
    output io : { flip d : UInt<8>, q : UInt<8>}

    reg reg : UInt, clock with :
      reset => (reset, UInt<1>("h0")) @[components.scala 35:20]
    reg <= io.d @[components.scala 36:7]
    io.q <= reg @[components.scala 37:8]

