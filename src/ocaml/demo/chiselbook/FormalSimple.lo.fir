FIRRTL version 2.0.0
circuit FormalSimple : 
  module FormalSimple : 
    input clock : Clock
    input reset1 : UInt<1>
    input io_a : UInt<10>
    input io_b : UInt<10>
    output io_y : UInt<10>
    node _io_y_T = and(io_a, io_b)
    io_y <= _io_y_T
