circuit GenHardware :
  module GenHardware :
    input clock : Clock
    input reset1 : UInt<1>
    output io_data_0 : UInt<8>
    output io_data_1 : UInt<8>
    output io_data_2 : UInt<8>
    output io_data_3 : UInt<8>
    output io_data_4 : UInt<8>
    output io_data_5 : UInt<8>
    output io_data_6 : UInt<8>
    output io_data_7 : UInt<8>
    output io_data_8 : UInt<8>
    output io_data_9 : UInt<8>
    output io_data_10 : UInt<8>
    output io_data_11 : UInt<8>
    output io_len : UInt<8>
    input io_squareIn : UInt<8>
    output io_squareOut : UInt<8>

    node _square_T = bits(io_squareIn, 2, 0)
    node squareROM_0 = UInt<5>("h0") @[GenHardware.scala 19:{26,26}]
    node _GEN_0 = validif(eq(UInt<1>("h0"), _square_T), squareROM_0) @[GenHardware.scala 27:{16,16}]
    node squareROM_1 = UInt<5>("h1") @[GenHardware.scala 19:{26,26}]
    node _GEN_1 = mux(eq(UInt<1>("h1"), _square_T), squareROM_1, _GEN_0) @[GenHardware.scala 27:{16,16}]
    node squareROM_2 = UInt<5>("h4") @[GenHardware.scala 19:{26,26}]
    node _GEN_2 = mux(eq(UInt<2>("h2"), _square_T), squareROM_2, _GEN_1) @[GenHardware.scala 27:{16,16}]
    node squareROM_3 = UInt<5>("h9") @[GenHardware.scala 19:{26,26}]
    node _GEN_3 = mux(eq(UInt<2>("h3"), _square_T), squareROM_3, _GEN_2) @[GenHardware.scala 27:{16,16}]
    node squareROM_4 = UInt<5>("h10") @[GenHardware.scala 19:{26,26}]
    node _GEN_4 = mux(eq(UInt<3>("h4"), _square_T), squareROM_4, _GEN_3) @[GenHardware.scala 27:{16,16}]
    node squareROM_5 = UInt<5>("h19") @[GenHardware.scala 19:{26,26}]
    node _GEN_5 = mux(eq(UInt<3>("h5"), _square_T), squareROM_5, _GEN_4) @[GenHardware.scala 27:{16,16}]
    node text_0 = UInt<7>("h48") @[GenHardware.scala 13:{21,21}]
    node text_1 = UInt<7>("h65") @[GenHardware.scala 13:{21,21}]
    node text_2 = UInt<7>("h6c") @[GenHardware.scala 13:{21,21}]
    node text_3 = UInt<7>("h6c") @[GenHardware.scala 13:{21,21}]
    node text_4 = UInt<7>("h6f") @[GenHardware.scala 13:{21,21}]
    node text_5 = UInt<7>("h20") @[GenHardware.scala 13:{21,21}]
    node text_6 = UInt<7>("h57") @[GenHardware.scala 13:{21,21}]
    node text_7 = UInt<7>("h6f") @[GenHardware.scala 13:{21,21}]
    node text_8 = UInt<7>("h72") @[GenHardware.scala 13:{21,21}]
    node text_9 = UInt<7>("h6c") @[GenHardware.scala 13:{21,21}]
    node text_10 = UInt<7>("h64") @[GenHardware.scala 13:{21,21}]
    node text_11 = UInt<7>("h21") @[GenHardware.scala 13:{21,21}]
    node _squareROM_square_T = _GEN_5 @[GenHardware.scala 27:16]
    io_data_0 <= pad(text_0, 8) @[GenHardware.scala 25:11]
    io_data_1 <= pad(text_1, 8) @[GenHardware.scala 25:11]
    io_data_2 <= pad(text_2, 8) @[GenHardware.scala 25:11]
    io_data_3 <= pad(text_3, 8) @[GenHardware.scala 25:11]
    io_data_4 <= pad(text_4, 8) @[GenHardware.scala 25:11]
    io_data_5 <= pad(text_5, 8) @[GenHardware.scala 25:11]
    io_data_6 <= pad(text_6, 8) @[GenHardware.scala 25:11]
    io_data_7 <= pad(text_7, 8) @[GenHardware.scala 25:11]
    io_data_8 <= pad(text_8, 8) @[GenHardware.scala 25:11]
    io_data_9 <= pad(text_9, 8) @[GenHardware.scala 25:11]
    io_data_10 <= pad(text_10, 8) @[GenHardware.scala 25:11]
    io_data_11 <= pad(text_11, 8) @[GenHardware.scala 25:11]
    io_len <= UInt<8>("hc") @[GenHardware.scala 26:10]
    io_squareOut <= pad(_squareROM_square_T, 8) @[GenHardware.scala 27:16]
