circuit MultiClockMemory :
  module MultiClockMemory :
    input clock : Clock
    input reset1 : UInt<1>
    input io_ps_0_clk : UInt<1>
    input io_ps_0_addr : UInt<10>
    input io_ps_0_datai : UInt<32>
    output io_ps_0_datao : UInt<32>
    input io_ps_0_en : UInt<1>
    input io_ps_0_we : UInt<1>

    mem ram : @[MultiClockMemory.scala 19:24]
      data-type => UInt<32>
      depth => 1024
      read-latency => 1
      write-latency => 1
      reader => datao_MPORT
      writer => MPORT
      read-under-write => new

    node _T = asClock(io_ps_0_clk) @[MultiClockMemory.scala 23:21]
    node _GEN_0 = validif(io_ps_0_we, io_ps_0_addr) @[MultiClockMemory.scala 27:20 28:14]
    node _GEN_1 = validif(io_ps_0_we, _T) @[MultiClockMemory.scala 27:20 28:14]
    node _GEN_2 = mux(io_ps_0_we, UInt<1>("h1"), UInt<1>("h0")) @[MultiClockMemory.scala 27:20 28:14 19:24]
    node _GEN_3 = validif(io_ps_0_we, UInt<1>("h1")) @[MultiClockMemory.scala 27:20 28:23]
    node _GEN_4 = validif(io_ps_0_we, io_ps_0_datai) @[MultiClockMemory.scala 27:20 28:23]
    node _GEN_5 = validif(io_ps_0_en, io_ps_0_addr) @[MultiClockMemory.scala 25:18 26:21]
    node _GEN_6 = validif(io_ps_0_en, _T) @[MultiClockMemory.scala 25:18 26:21]
    node _GEN_7 = mux(io_ps_0_en, UInt<1>("h1"), UInt<1>("h0")) @[MultiClockMemory.scala 25:18 26:21 19:24]
    node _GEN_8 = mux(io_ps_0_en, ram.datao_MPORT.data, UInt<32>("h0")) @[MultiClockMemory.scala 25:18 26:15 24:30]
    node _GEN_9 = validif(io_ps_0_en, _GEN_0) @[MultiClockMemory.scala 25:18]
    node _GEN_10 = validif(io_ps_0_en, _GEN_1) @[MultiClockMemory.scala 25:18]
    node _GEN_11 = mux(io_ps_0_en, _GEN_2, UInt<1>("h0")) @[MultiClockMemory.scala 25:18 19:24]
    node _GEN_12 = validif(io_ps_0_en, _GEN_3) @[MultiClockMemory.scala 25:18]
    node _GEN_13 = validif(io_ps_0_en, _GEN_4) @[MultiClockMemory.scala 25:18]

    node datao = _GEN_8 @[MultiClockMemory.scala 24:30]
    io_ps_0_datao <= datao @[MultiClockMemory.scala 31:15]
    ram.datao_MPORT.addr <= _GEN_5
    ram.datao_MPORT.en <= _GEN_7
    ram.datao_MPORT.clk <= _GEN_6

    ram.MPORT.addr <= _GEN_9
    ram.MPORT.en <= _GEN_11
    ram.MPORT.clk <= _GEN_10
    ram.MPORT.data <= _GEN_13
    ram.MPORT.mask <= _GEN_12

