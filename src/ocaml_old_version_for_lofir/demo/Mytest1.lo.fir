circuit TopOfVisualizer : @[:@2.0]
  module VizModC : @[:@3.2]
    input clock : Clock @[:@4.4]
    input reset1 : UInt<1> @[:@5.4]
    input io_in : UInt<16> @[:@6.4]
    output io_out : UInt<16> @[:@6.4]
  
    skip
    io_out <= io_in

  module VizModA : @[:@13.2]
    input clock : Clock @[:@14.4]
    input reset1 : UInt<1> @[:@15.4]
    input io_in : UInt<32> @[:@16.4]
    output io_out : UInt<16> @[:@16.4]

    inst modC aof VizModC @[VisualizerSpec.scala 40:20:@21.4]
    io_out <= modC.io_out
    modC.io_in <= bits(io_in, 15, 0)
    modC.clock <= clock
    modC.reset1 <= reset1

  module TopOfVisualizer : @[:@28.2]
    input clock : Clock @[:@29.4]
    input reset1 : UInt<1> @[:@30.4]
    input io_in1 : UInt<32> @[:@31.4]
    input io_in2 : UInt<32> @[:@31.4]
    input io_select : UInt<1> @[:@31.4]
    output io_out : UInt<32> @[:@31.4]
    output io_out0 : UInt<16> @[:@31.4]

    reg x : UInt<32>, clock with :
      reset => (UInt<1>("h0"), x) @[VisualizerSpec.scala 65:14:@36.4]
    reg y : UInt<32>, clock with :
      reset => (UInt<1>("h0"), y) @[VisualizerSpec.scala 66:14:@37.4]
    
    inst modA aof VizModA @[VisualizerSpec.scala 70:20:@39.4]

    node _GEN_0 = mux(io_select, io_in1, x) @[VisualizerSpec.scala 75:19:@43.4]
    node _T_14 = eq(io_select, UInt<1>("h0")) @[VisualizerSpec.scala 75:19:@49.4]
    node _GEN_5 = mux(_T_14, io_in2, _GEN_0) @[VisualizerSpec.scala 79:14:@50.4]
    io_out0 <= modA.io_out
    node _T_17 = add(io_out0, io_in2) @[VisualizerSpec.scala 86:20:@57.4]
    node _T_18 = tail(_T_17, 1) @[VisualizerSpec.scala 86:20:@58.4]
    io_out <= y
    modA.io_in <= x
    modA.clock <= clock
    modA.reset1 <= reset1
    x <= _GEN_5
    y <= _T_18
