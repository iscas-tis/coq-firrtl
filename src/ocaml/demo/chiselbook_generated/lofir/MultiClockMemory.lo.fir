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
    input io_ps_1_clk : UInt<1>
    input io_ps_1_addr : UInt<10>
    input io_ps_1_datai : UInt<32>
    output io_ps_1_datao : UInt<32>
    input io_ps_1_en : UInt<1>
    input io_ps_1_we : UInt<1>
    input io_ps_2_clk : UInt<1>
    input io_ps_2_addr : UInt<10>
    input io_ps_2_datai : UInt<32>
    output io_ps_2_datao : UInt<32>
    input io_ps_2_en : UInt<1>
    input io_ps_2_we : UInt<1>

    mem ram : @[MultiClockMemory.scala 19:24]
      data-type => UInt<32>
      depth => 1024
      read-latency => 1
      write-latency => 1
      reader => datao_MPORT
      reader => datao_MPORT_1
      reader => datao_MPORT_2
      writer => MPORT
      writer => MPORT_1
      writer => MPORT_2
      read-under-write => undefined
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
    node _T_1 = asClock(io_ps_1_clk) @[MultiClockMemory.scala 23:21]
    node _GEN_14 = validif(io_ps_1_we, io_ps_1_addr) @[MultiClockMemory.scala 27:20 28:14]
    node _GEN_15 = validif(io_ps_1_we, _T_1) @[MultiClockMemory.scala 27:20 28:14]
    node _GEN_16 = mux(io_ps_1_we, UInt<1>("h1"), UInt<1>("h0")) @[MultiClockMemory.scala 27:20 28:14 19:24]
    node _GEN_17 = validif(io_ps_1_we, UInt<1>("h1")) @[MultiClockMemory.scala 27:20 28:23]
    node _GEN_18 = validif(io_ps_1_we, io_ps_1_datai) @[MultiClockMemory.scala 27:20 28:23]
    node _GEN_19 = validif(io_ps_1_en, io_ps_1_addr) @[MultiClockMemory.scala 25:18 26:21]
    node _GEN_20 = validif(io_ps_1_en, _T_1) @[MultiClockMemory.scala 25:18 26:21]
    node _GEN_21 = mux(io_ps_1_en, UInt<1>("h1"), UInt<1>("h0")) @[MultiClockMemory.scala 25:18 26:21 19:24]
    node _GEN_22 = mux(io_ps_1_en, ram.datao_MPORT_1.data, UInt<32>("h0")) @[MultiClockMemory.scala 25:18 26:15 24:30]
    node _GEN_23 = validif(io_ps_1_en, _GEN_14) @[MultiClockMemory.scala 25:18]
    node _GEN_24 = validif(io_ps_1_en, _GEN_15) @[MultiClockMemory.scala 25:18]
    node _GEN_25 = mux(io_ps_1_en, _GEN_16, UInt<1>("h0")) @[MultiClockMemory.scala 25:18 19:24]
    node _GEN_26 = validif(io_ps_1_en, _GEN_17) @[MultiClockMemory.scala 25:18]
    node _GEN_27 = validif(io_ps_1_en, _GEN_18) @[MultiClockMemory.scala 25:18]
    node _T_2 = asClock(io_ps_2_clk) @[MultiClockMemory.scala 23:21]
    node _GEN_28 = validif(io_ps_2_we, io_ps_2_addr) @[MultiClockMemory.scala 27:20 28:14]
    node _GEN_29 = validif(io_ps_2_we, _T_2) @[MultiClockMemory.scala 27:20 28:14]
    node _GEN_30 = mux(io_ps_2_we, UInt<1>("h1"), UInt<1>("h0")) @[MultiClockMemory.scala 27:20 28:14 19:24]
    node _GEN_31 = validif(io_ps_2_we, UInt<1>("h1")) @[MultiClockMemory.scala 27:20 28:23]
    node _GEN_32 = validif(io_ps_2_we, io_ps_2_datai) @[MultiClockMemory.scala 27:20 28:23]
    node _GEN_33 = validif(io_ps_2_en, io_ps_2_addr) @[MultiClockMemory.scala 25:18 26:21]
    node _GEN_34 = validif(io_ps_2_en, _T_2) @[MultiClockMemory.scala 25:18 26:21]
    node _GEN_35 = mux(io_ps_2_en, UInt<1>("h1"), UInt<1>("h0")) @[MultiClockMemory.scala 25:18 26:21 19:24]
    node _GEN_36 = mux(io_ps_2_en, ram.datao_MPORT_2.data, UInt<32>("h0")) @[MultiClockMemory.scala 25:18 26:15 24:30]
    node _GEN_37 = validif(io_ps_2_en, _GEN_28) @[MultiClockMemory.scala 25:18]
    node _GEN_38 = validif(io_ps_2_en, _GEN_29) @[MultiClockMemory.scala 25:18]
    node _GEN_39 = mux(io_ps_2_en, _GEN_30, UInt<1>("h0")) @[MultiClockMemory.scala 25:18 19:24]
    node _GEN_40 = validif(io_ps_2_en, _GEN_31) @[MultiClockMemory.scala 25:18]
    node _GEN_41 = validif(io_ps_2_en, _GEN_32) @[MultiClockMemory.scala 25:18]
    node datao = _GEN_8 @[MultiClockMemory.scala 24:30]
    node datao_1 = _GEN_22 @[MultiClockMemory.scala 24:30]
    node datao_2 = _GEN_36 @[MultiClockMemory.scala 24:30]
    io_ps_0_datao <= datao @[MultiClockMemory.scala 31:15]
    io_ps_1_datao <= datao_1 @[MultiClockMemory.scala 31:15]
    io_ps_2_datao <= datao_2 @[MultiClockMemory.scala 31:15]
    ram.datao_MPORT.addr <= _GEN_5
    ram.datao_MPORT.en <= _GEN_7
    ram.datao_MPORT.clk <= _GEN_6
    ram.datao_MPORT_1.addr <= _GEN_19
    ram.datao_MPORT_1.en <= _GEN_21
    ram.datao_MPORT_1.clk <= _GEN_20
    ram.datao_MPORT_2.addr <= _GEN_33
    ram.datao_MPORT_2.en <= _GEN_35
    ram.datao_MPORT_2.clk <= _GEN_34
    ram.MPORT.addr <= _GEN_9
    ram.MPORT.en <= _GEN_11
    ram.MPORT.clk <= _GEN_10
    ram.MPORT.data <= _GEN_13
    ram.MPORT.mask <= _GEN_12
    ram.MPORT_1.addr <= _GEN_23
    ram.MPORT_1.en <= _GEN_25
    ram.MPORT_1.clk <= _GEN_24
    ram.MPORT_1.data <= _GEN_27
    ram.MPORT_1.mask <= _GEN_26
    ram.MPORT_2.addr <= _GEN_37
    ram.MPORT_2.en <= _GEN_39
    ram.MPORT_2.clk <= _GEN_38
    ram.MPORT_2.data <= _GEN_41
    ram.MPORT_2.mask <= _GEN_40
