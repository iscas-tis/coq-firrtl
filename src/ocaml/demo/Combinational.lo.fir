circuit Combinational : @[:@2.0]
  module Combinational : @[:@3.2]
    input clock : Clock @[:@4.4]
    input reset1 : UInt < 1 > @[:@5.4]
    input io_x : UInt < 16 > @[:@6.4]
    input io_y : UInt < 16 > @[:@6.4]
    output io_z : UInt < 16 > @[:@6.4]

    node _T_11 = add ( io_x , io_y ) @[Combinational.scala 12:16:@8.4]
    node _T_12 = tail ( _T_11 , 1 ) @[Combinational.scala 12:16:@9.4]
    io_z <= _T_12 @[Combinational.scala 12:8:@10.4]
    skip
