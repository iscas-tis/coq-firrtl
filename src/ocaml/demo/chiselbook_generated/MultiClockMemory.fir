circuit MultiClockMemory :
  module MultiClockMemory :
    input clock : Clock
    input reset : UInt<1>
    output io : { ps : { flip clk : UInt<1>, flip addr : UInt<10>, flip datai : UInt<32>, datao : UInt<32>, flip en : UInt<1>, flip we : UInt<1>}[3]}

    smem ram : UInt<32> [1024] @[MultiClockMemory.scala 19:24]
    node _T = asClock(io.ps[0].clk) @[MultiClockMemory.scala 23:21]
    wire datao : UInt<32> @[MultiClockMemory.scala 24:30]
    datao <= UInt<32>("h0") @[MultiClockMemory.scala 24:30]
    when io.ps[0].en : @[MultiClockMemory.scala 25:18]
      infer mport datao_MPORT = ram[io.ps[0].addr], _T @[MultiClockMemory.scala 26:21]
      datao <= datao_MPORT @[MultiClockMemory.scala 26:15]
      when io.ps[0].we : @[MultiClockMemory.scala 27:20]
        infer mport MPORT = ram[io.ps[0].addr], _T @[MultiClockMemory.scala 28:14]
        MPORT <= io.ps[0].datai @[MultiClockMemory.scala 28:23]
    io.ps[0].datao <= datao @[MultiClockMemory.scala 31:15]
    node _T_1 = asClock(io.ps[1].clk) @[MultiClockMemory.scala 23:21]
    wire datao_1 : UInt<32> @[MultiClockMemory.scala 24:30]
    datao_1 <= UInt<32>("h0") @[MultiClockMemory.scala 24:30]
    when io.ps[1].en : @[MultiClockMemory.scala 25:18]
      infer mport datao_MPORT_1 = ram[io.ps[1].addr], _T_1 @[MultiClockMemory.scala 26:21]
      datao_1 <= datao_MPORT_1 @[MultiClockMemory.scala 26:15]
      when io.ps[1].we : @[MultiClockMemory.scala 27:20]
        infer mport MPORT_1 = ram[io.ps[1].addr], _T_1 @[MultiClockMemory.scala 28:14]
        MPORT_1 <= io.ps[1].datai @[MultiClockMemory.scala 28:23]
    io.ps[1].datao <= datao_1 @[MultiClockMemory.scala 31:15]
    node _T_2 = asClock(io.ps[2].clk) @[MultiClockMemory.scala 23:21]
    wire datao_2 : UInt<32> @[MultiClockMemory.scala 24:30]
    datao_2 <= UInt<32>("h0") @[MultiClockMemory.scala 24:30]
    when io.ps[2].en : @[MultiClockMemory.scala 25:18]
      infer mport datao_MPORT_2 = ram[io.ps[2].addr], _T_2 @[MultiClockMemory.scala 26:21]
      datao_2 <= datao_MPORT_2 @[MultiClockMemory.scala 26:15]
      when io.ps[2].we : @[MultiClockMemory.scala 27:20]
        infer mport MPORT_2 = ram[io.ps[2].addr], _T_2 @[MultiClockMemory.scala 28:14]
        MPORT_2 <= io.ps[2].datai @[MultiClockMemory.scala 28:23]
    io.ps[2].datao <= datao_2 @[MultiClockMemory.scala 31:15]

