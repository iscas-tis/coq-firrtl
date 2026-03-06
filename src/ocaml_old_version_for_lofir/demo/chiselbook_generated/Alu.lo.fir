circuit Alu :
  module Alu :
    input clock : Clock
    input reset1 : UInt<1>
    input io_a : UInt<16>
    input io_b : UInt<16>
    input io_fn : UInt<2>
    output io_y : UInt<16>

    node _T = eq(UInt<1>("h0"), io_fn) @[components.scala 182:17]
    node _io_y_T = add(io_a, io_b) @[components.scala 183:28]
    node _io_y_T_1 = tail(_io_y_T, 1) @[components.scala 183:28]
    node _T_1 = eq(UInt<1>("h1"), io_fn) @[components.scala 182:17]
    node _io_y_T_2 = sub(io_a, io_b) @[components.scala 184:28]
    node _io_y_T_3 = tail(_io_y_T_2, 1) @[components.scala 184:28]
    node _T_2 = eq(UInt<2>("h2"), io_fn) @[components.scala 182:17]
    node _io_y_T_4 = or(io_a, io_b) @[components.scala 185:28]
    node _T_3 = eq(UInt<2>("h3"), io_fn) @[components.scala 182:17]
    node _io_y_T_5 = and(io_a, io_b) @[components.scala 186:28]
    node _GEN_0 = mux(_T_3, _io_y_T_5, UInt<1>("h0")) @[components.scala 182:17 186:20 179:8]
    node _GEN_1 = mux(_T_2, _io_y_T_4, _GEN_0) @[components.scala 182:17 185:20]
    node _GEN_2 = mux(_T_1, _io_y_T_3, _GEN_1) @[components.scala 182:17 184:20]
    node _GEN_3 = mux(_T, _io_y_T_1, _GEN_2) @[components.scala 182:17 183:20]
    io_y <= _GEN_3
