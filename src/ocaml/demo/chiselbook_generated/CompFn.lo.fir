circuit CompFn :
  module CompFn :
    input clock : Clock
    input reset1 : UInt<1>
    input io_a : UInt<4>
    input io_b : UInt<4>
    output io_out : UInt<4>
    input io_c : UInt<4>
    input io_d : UInt<4>
    output io_out2 : UInt<4>
    input io_del : UInt<4>
    output io_out3 : UInt<4>

    node _x_T = add(io_a, io_b) @[components.scala 217:7]
    node x = tail(_x_T, 1) @[components.scala 217:7]
    node _y_T = add(io_c, io_d) @[components.scala 217:7]
    node y = tail(_y_T, 1) @[components.scala 217:7]
    node _io_out2_T = sub(y, UInt<1>("h1")) @[components.scala 228:16]
    node _io_out2_T_1 = tail(_io_out2_T, 1) @[components.scala 228:16]
    reg delOut_REG : UInt<4>, clock with :
      reset => (UInt<1>("h0"), delOut_REG) @[components.scala 233:31]
    reg delOut : UInt<4>, clock with :
      reset => (UInt<1>("h0"), delOut) @[components.scala 233:31]
    io_out <= x @[components.scala 227:10]
    io_out2 <= _io_out2_T_1 @[components.scala 228:11]
    io_out3 <= delOut @[components.scala 240:11]
    delOut_REG <= io_del @[components.scala 233:31]
    delOut <= delOut_REG @[components.scala 233:31]
