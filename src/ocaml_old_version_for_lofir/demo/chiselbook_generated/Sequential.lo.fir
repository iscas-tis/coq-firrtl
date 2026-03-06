circuit Sequential :
  module Sequential :
    input clock : Clock
    input reset1 : UInt<1>
    input io_d : UInt<4>
    output io_q : UInt<4>
    input io_d2 : UInt<4>
    output io_q2 : UInt<4>
    input io_d3 : UInt<4>
    output io_q3 : UInt<4>
    input io_ena : UInt<1>
    output io_q4 : UInt<4>
    output io_q5 : UInt<4>
    output io_q6 : UInt<4>
    output io_q7 : UInt<4>
    input io_riseIn : UInt<1>
    output io_riseOut : UInt<1>

    reg q : UInt<4>, clock with :
      reset => (UInt<1>("h0"), q) @[Sequential.scala 23:18]
    reg delayReg : UInt<4>, clock with :
      reset => (UInt<1>("h0"), delayReg) @[Sequential.scala 29:21]
    reg valReg : UInt<4>, clock with :
      reset => (UInt<1>("h0"), valReg) @[Sequential.scala 37:23]
    reg enableReg : UInt<4>, clock with :
      reset => (UInt<1>("h0"), enableReg) @[Sequential.scala 45:22]
    node _GEN_0 = mux(io_ena, io_d3, enableReg) @[Sequential.scala 47:17 48:15 45:22]
    reg resetEnableReg : UInt<4>, clock with :
      reset => (UInt<1>("h0"), resetEnableReg) @[Sequential.scala 54:31]
    node _GEN_1 = mux(io_ena, io_d3, resetEnableReg) @[Sequential.scala 56:17 57:20 54:31]
    reg enableReg2 : UInt<4>, clock with :
      reset => (UInt<1>("h0"), enableReg2) @[Reg.scala 19:16]
    node _GEN_2 = mux(io_ena, io_d3, enableReg2) @[Reg.scala 19:16 20:{18,22}]
    reg resetEnableReg2 : UInt<4>, clock with :
      reset => (UInt<1>("h0"), resetEnableReg2) @[Reg.scala 35:20]
    node _GEN_3 = mux(io_ena, io_d3, resetEnableReg2) @[Reg.scala 36:18 35:20 36:22]
    reg risingEdge_REG : UInt<1>, clock with :
      reset => (UInt<1>("h0"), risingEdge_REG) @[Sequential.scala 74:34]
    node _risingEdge_T = eq(risingEdge_REG, UInt<1>("h0")) @[Sequential.scala 74:26]
    node risingEdge = and(io_riseIn, _risingEdge_T) @[Sequential.scala 74:24]
    io_q <= q @[Sequential.scala 25:8]
    io_q2 <= delayReg @[Sequential.scala 33:9]
    io_q3 <= valReg @[Sequential.scala 41:9]
    io_q4 <= enableReg @[Sequential.scala 51:9]
    io_q5 <= resetEnableReg @[Sequential.scala 60:9]
    io_q6 <= enableReg2 @[Sequential.scala 65:9]
    io_q7 <= resetEnableReg2 @[Sequential.scala 70:9]
    io_riseOut <= risingEdge @[Sequential.scala 76:14]
    q <= io_d @[Sequential.scala 23:18]
    delayReg <= io_d2 @[Sequential.scala 31:12]
    valReg <= mux(reset1, UInt<4>("h0"), io_d3) @[Sequential.scala 37:{23,23} 39:10]
    enableReg <= _GEN_0
    resetEnableReg <= mux(reset1, UInt<4>("h0"), _GEN_1) @[Sequential.scala 54:{31,31}]
    enableReg2 <= _GEN_2
    resetEnableReg2 <= mux(reset1, UInt<4>("h0"), _GEN_3) @[Reg.scala 35:{20,20}]
    risingEdge_REG <= io_riseIn @[Sequential.scala 74:34]
