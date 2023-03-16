circuit Registers :
  module Registers :
    input clock : Clock
    input reset1 : UInt<1>
    input io_in : UInt<8>
    output io_out : UInt<8>

    reg q : UInt<8>, clock with :
      reset => (UInt<1>("h0"), q) @[Registers.scala 10:20]
    reg nextReg : UInt<8>, clock with :
      reset => (UInt<1>("h0"), nextReg) @[Registers.scala 20:24]
    reg bothReg : UInt<8>, clock with :
      reset => (UInt<1>("h0"), bothReg) @[Registers.scala 24:24]
    io_out <= q @[Registers.scala 26:10]
    q <= mux(reset1, UInt<8>("h0"), io_in) @[Registers.scala 10:{20,20} 15:7]
    nextReg <= io_in @[Registers.scala 20:24]
    bothReg <= mux(reset1, UInt<1>("h0"), io_in) @[Registers.scala 24:{24,24,24}]
