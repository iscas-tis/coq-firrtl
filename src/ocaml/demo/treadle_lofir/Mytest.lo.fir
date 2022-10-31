circuit Mytest : @[:@2.0]
  module Mytest : @[:@3.2]
    input clock : Clock @[:@4.4]
    input reset1 : UInt<1> @[:@5.4]
    input io_in1 : UInt<32> @[:@6.4]
    output io_out1 : UInt<32> @[:@6.4]
    output io_out2 : UInt<32> @[:@6.4]
    output io_out3 : UInt<32> @[:@6.4]
    output io_out4 : UInt<32> @[:@6.4]
    output io_out5 : UInt<32> @[:@6.4]
    output io_out6 : UInt<32> @[:@6.4]
    output io_out7 : UInt<32> @[:@6.4]
    output io_out8 : UInt<32> @[:@6.4]
  
    node _T_20 = pad(io_in1, 32) @[ALUTester.scala 38:32:@12.4]
    node _T_21 = cvt(_T_20) @[ALUTester.scala 38:32:@13.4]
    node _T_22 = andr(_T_21) @[ALUTester.scala 40:32:@17.4]
    node _T_23 = orr(_T_22) @[ALUTester.scala 41:31:@18.4]
    node _T_24 = xorr(_T_23) @[ALUTester.scala 42:32:@19.4]
    node _T_25 = ahead(_T_24, 1) @[ALUTester.scala 38:32:@13.4]
    
    node _T_60 = leq(UInt<3>("h4"), _T_25) @[Mux.scala 46:19:@52.4]
    node _T_62 = neq(UInt<2>("h3"), _T_60) @[Mux.scala 46:19:@54.4]
    
    io_out1 <= _T_20
    io_out2 <= _T_21
    io_out3 <= _T_22
    io_out4 <= _T_23
    io_out5 <= _T_24
    io_out6 <= _T_25
    io_out7 <= _T_60
    io_out8 <= _T_62
