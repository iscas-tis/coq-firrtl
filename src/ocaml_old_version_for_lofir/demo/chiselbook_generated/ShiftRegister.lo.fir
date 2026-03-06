circuit ShiftRegister :
  module ShiftRegister :
    input clock : Clock
    input reset1 : UInt<1>
    input io_din : UInt<1>
    output io_dout : UInt<1>
    input io_serIn : UInt<1>
    output io_paraOut : UInt<4>
    input io_d : UInt<4>
    input io_load : UInt<1>
    output io_serOut : UInt<1>

    reg shiftReg : UInt<4>, clock with :
      reset => (UInt<1>("h0"), shiftReg) @[ShiftRegister.scala 18:21]
    node _shiftReg_T = bits(shiftReg, 2, 0) @[ShiftRegister.scala 19:23]
    node _shiftReg_T_1 = cat(_shiftReg_T, io_din) @[ShiftRegister.scala 19:30]
    node dout = bits(shiftReg, 3, 3) @[ShiftRegister.scala 20:22]
    reg outReg : UInt<4>, clock with :
      reset => (UInt<1>("h0"), outReg) @[ShiftRegister.scala 28:23]
    node _outReg_T = bits(outReg, 3, 1) @[ShiftRegister.scala 29:28]
    node _outReg_T_1 = cat(io_serIn, _outReg_T) @[ShiftRegister.scala 29:19]
    reg loadReg : UInt<4>, clock with :
      reset => (UInt<1>("h0"), loadReg) @[ShiftRegister.scala 36:24]
    node _loadReg_T = bits(loadReg, 3, 1) @[ShiftRegister.scala 40:30]
    node _loadReg_T_1 = cat(UInt<1>("h0"), _loadReg_T) @[ShiftRegister.scala 40:20]
    node _GEN_0 = mux(io_load, io_d, _loadReg_T_1) @[ShiftRegister.scala 37:15 38:13 40:13]
    node serOut = bits(loadReg, 0, 0) @[ShiftRegister.scala 42:23]
    io_dout <= dout @[ShiftRegister.scala 48:11]
    io_paraOut <= outReg @[ShiftRegister.scala 47:14]
    io_serOut <= serOut @[ShiftRegister.scala 45:13]
    shiftReg <= _shiftReg_T_1 @[ShiftRegister.scala 19:12]
    outReg <= mux(reset1, UInt<4>("h0"), _outReg_T_1) @[ShiftRegister.scala 28:{23,23} 29:10]
    loadReg <= mux(reset1, UInt<4>("h0"), _GEN_0) @[ShiftRegister.scala 36:{24,24}]
