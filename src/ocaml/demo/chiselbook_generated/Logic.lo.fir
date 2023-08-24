FIRRTL version 1.1.0
circuit Logic :
  module Logic :
    input clock : Clock
    input reset : UInt<1>
    input io_a : UInt<1>
    input io_b : UInt<1>
    input io_c : UInt<1>
    output io_out : UInt<1>
    output io_cat : UInt<16>
    output io_ch : UInt<8>
    output io_word : UInt<16>
    output io_result : UInt<4>

    node _logic_T = and(io_a, io_b) @[Logic.scala 59:18]
    node logic = or(_logic_T, io_c) @[Logic.scala 59:23]
    node bop = and(UInt<1>("h1"), UInt<1>("h0")) @[Logic.scala 67:16]
    node and = and(io_a, io_b) @[Logic.scala 70:15]
    node or = or(io_a, io_b) @[Logic.scala 71:14]
    node xor = xor(io_a, io_b) @[Logic.scala 72:15]
    node not = not(io_a) @[Logic.scala 73:13]
    node _add_T = add(io_a, io_b) @[Logic.scala 77:15]
    node add = tail(_add_T, 1) @[Logic.scala 77:15]
    node _sub_T = sub(io_a, io_b) @[Logic.scala 78:15]
    node sub = tail(_sub_T, 1) @[Logic.scala 78:15]
    node _neg_T = sub(UInt<1>("h0"), io_a) @[Logic.scala 79:13]
    node neg = tail(_neg_T, 1) @[Logic.scala 79:13]
    node mul = mul(io_a, io_b) @[Logic.scala 80:15]
    node div = div(io_a, io_b) @[Logic.scala 81:15]
    node mod = rem(io_a, io_b) @[Logic.scala 82:15]
    node _w_T = and(io_a, io_b) @[Logic.scala 88:10]
    node word = cat(UInt<8>("hff"), UInt<8>("h1")) @[Logic.scala 104:23]
    node sel = eq(io_b, io_c) @[Logic.scala 108:15]
    node result = mux(sel, io_a, io_b) @[Logic.scala 110:19]
    node split_high = UInt<8>("hff") @[Logic.scala 130:19 132:14]
    node split_low = UInt<8>("h1") @[Logic.scala 130:19 131:13]
    node _assignWord_T = cat(split_high, split_low) @[Logic.scala 134:29]
    node vecResult_1 = UInt<1>("h0") @[Logic.scala 140:23 144:16]
    node vecResult_0 = UInt<1>("h1") @[Logic.scala 140:23 143:16]
    node uintResult_lo = cat(vecResult_1, vecResult_0) @[Logic.scala 148:30]
    node vecResult_3 = UInt<1>("h0") @[Logic.scala 140:23 146:16]
    node vecResult_2 = UInt<1>("h1") @[Logic.scala 140:23 145:16]
    node uintResult_hi = cat(vecResult_3, vecResult_2) @[Logic.scala 148:30]
    node uintResult = cat(uintResult_hi, uintResult_lo) @[Logic.scala 148:30]
    node w = _w_T @[Logic.scala 86:15 88:5]
    node assignWord = _assignWord_T @[Logic.scala 123:24 134:14]
    io_out <= logic @[Logic.scala 62:10]
    io_cat <= word @[Logic.scala 106:10]
    io_ch <= UInt<8>("h41") @[Logic.scala 47:9]
    io_word <= assignWord @[Logic.scala 136:11]
    io_result <= uintResult @[Logic.scala 150:13]
