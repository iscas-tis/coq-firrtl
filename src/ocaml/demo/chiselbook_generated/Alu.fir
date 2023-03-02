circuit Alu :
  module Alu :
    input clock : Clock
    input reset : UInt<1>
    output io : { flip a : UInt<16>, flip b : UInt<16>, flip fn : UInt<2>, y : UInt<16>}

    io.y <= UInt<1>("h0") @[components.scala 179:8]
    node _T = eq(UInt<1>("h0"), io.fn) @[components.scala 182:17]
    when _T : @[components.scala 182:17]
      node _io_y_T = add(io.a, io.b) @[components.scala 183:28]
      node _io_y_T_1 = tail(_io_y_T, 1) @[components.scala 183:28]
      io.y <= _io_y_T_1 @[components.scala 183:20]
    else :
      node _T_1 = eq(UInt<1>("h1"), io.fn) @[components.scala 182:17]
      when _T_1 : @[components.scala 182:17]
        node _io_y_T_2 = sub(io.a, io.b) @[components.scala 184:28]
        node _io_y_T_3 = tail(_io_y_T_2, 1) @[components.scala 184:28]
        io.y <= _io_y_T_3 @[components.scala 184:20]
      else :
        node _T_2 = eq(UInt<2>("h2"), io.fn) @[components.scala 182:17]
        when _T_2 : @[components.scala 182:17]
          node _io_y_T_4 = or(io.a, io.b) @[components.scala 185:28]
          io.y <= _io_y_T_4 @[components.scala 185:20]
        else :
          node _T_3 = eq(UInt<2>("h3"), io.fn) @[components.scala 182:17]
          when _T_3 : @[components.scala 182:17]
            node _io_y_T_5 = and(io.a, io.b) @[components.scala 186:28]
            io.y <= _io_y_T_5 @[components.scala 186:20]


