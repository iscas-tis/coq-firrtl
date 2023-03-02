circuit CompFn :
  module CompFn :
    input clock : Clock
    input reset : UInt<1>
    output io : { flip a : UInt<4>, flip b : UInt<4>, out : UInt<4>, flip c : UInt<4>, flip d : UInt<4>, out2 : UInt<4>, flip del : UInt<4>, out3 : UInt<4>}

    node _x_T = add(io.a, io.b) @[components.scala 217:7]
    node x = tail(_x_T, 1) @[components.scala 217:7]
    node _y_T = add(io.c, io.d) @[components.scala 217:7]
    node y = tail(_y_T, 1) @[components.scala 217:7]
    io.out <= x @[components.scala 227:10]
    node _io_out2_T = sub(y, UInt<1>("h1")) @[components.scala 228:16]
    node _io_out2_T_1 = tail(_io_out2_T, 1) @[components.scala 228:16]
    io.out2 <= _io_out2_T_1 @[components.scala 228:11]
    reg delOut_REG : UInt, clock with :
      reset => (UInt<1>("h0"), delOut_REG) @[components.scala 233:31]
    delOut_REG <= io.del @[components.scala 233:31]
    reg delOut : UInt, clock with :
      reset => (UInt<1>("h0"), delOut) @[components.scala 233:31]
    delOut <= delOut_REG @[components.scala 233:31]
    io.out3 <= delOut @[components.scala 240:11]

