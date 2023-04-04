circuit Logic :
  module Logic :
    input io_a : SInt<4>
    input io_b : SInt<3>
    output io_out1 : SInt<7>

    node mul1 = mul(io_a, io_b) @[Logic.scala 80:15]
    io_out1 <= mul1 @[Logic.scala 62:10] 

