circuit TopOfVisualizer : @[:@2.0]
  module VizModC : @[:@3.2]
    input clock : Clock @[:@4.4]
    input reset1 : UInt < 1 > @[:@5.4]
    input io_in : UInt < 16 > @[:@6.4]
    output io_out : UInt < 16 > @[:@6.4]
  
    skip 
    io_out <= io_in 

  module VizModA : @[:@13.2]
    input clock : Clock @[:@14.4]
    input reset1 : UInt < 1 > @[:@15.4]
    input io_in : UInt < 32 > @[:@16.4]
    output io_out : UInt < 16 > @[:@16.4]
  
    inst modC of VizModC @[VisualizerSpec.scala 40:20:@21.4]
    io_out <= modC.io_out 
    modC.io_in <= bits(io_in , 15 , 0 ) 
    modC.clock <= clock 
    modC.reset1 <= reset1 

  module TopOfVisualizer : @[:@28.2]
    input clock : Clock @[:@29.4]
    input reset1 : UInt < 1 > @[:@30.4]
    input io_in1 : UInt < 32 > @[:@31.4]
    input io_in2 : UInt < 32 > @[:@31.4]
    input io_select : UInt < 1 > @[:@31.4]
    output io_out : UInt < 32 > @[:@31.4]
    output io_memOut : UInt < 32 > @[:@31.4]
  
    reg x : UInt < 32 > , clock with : 
      reset => (UInt < 1 > ( "h0" ) , x ) @[VisualizerSpec.scala 65:14:@36.4]
    reg y : UInt < 32 > , clock with : 
      reset => (UInt < 1 > ( "h0" ) , y ) @[VisualizerSpec.scala 66:14:@37.4]
    mem myMem : @[VisualizerSpec.scala 68:18:@38.4]
      data-type => UInt < 32 > 
      depth => 16 
      read-latency => 0 
      write-latency => 1 
      reader => _T_16 
      writer => _T_12 
      read-under-write => undefined 
    inst modA of VizModA @[VisualizerSpec.scala 70:20:@39.4]
    node _T_11 = bits(io_in1 , 3 , 0) @[:@45.6]
    node _GEN_0 = mux(io_select , io_in1 , x) @[VisualizerSpec.scala 75:19:@43.4]
    node _GEN_1 = validif(io_select , _T_11) @[VisualizerSpec.scala 75:19:@43.4]
    node _GEN_2 = validif(io_select , clock) @[VisualizerSpec.scala 75:19:@43.4]
    node _GEN_3 = mux(io_select , UInt < 1 > ( "h1" ) , UInt < 1 > ( "h0" ) ) @[VisualizerSpec.scala 75:19:@43.4]
    node _GEN_4 = validif(io_select , io_in2) @[VisualizerSpec.scala 75:19:@43.4]
    node _T_14 = eq(io_select , UInt < 1 > ( "h0" ) ) @[VisualizerSpec.scala 75:19:@49.4]
    node _T_15 = bits(io_in1 , 3 , 0) @[:@52.6]
    node _GEN_5 = mux(_T_14 , io_in2 , _GEN_0) @[VisualizerSpec.scala 79:14:@50.4]
    