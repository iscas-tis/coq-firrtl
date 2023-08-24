circuit BundleVec :
  module BundleVec :
    input clock : Clock
    input reset1 : UInt<1>
    output io_chan_data : UInt<32>
    output io_chan_valid : UInt<1>
    output io_chan2_data : UInt<32>
    output io_chan2_valid : UInt<1>
    input io_idx : UInt<4>
    output io_array : UInt<4>
    input io_dIn : UInt<32>
    output io_dOut : UInt<32>
    output io_bvOut : UInt<8>
    output io_chreg_data : UInt<32>
    output io_chreg_valid : UInt<1>
    input io_din : UInt<8>
    output io_dout : UInt<8>
    input io_rdIdx : UInt<2>
    input io_wrIdx : UInt<2>
    input io_selMux : UInt<2>
    output io_muxOut : UInt<8>
    input io_selVec : UInt<5>
    input io_selVecCond : UInt<1>
    output io_defVecOut : UInt<3>
    input io_defVecSigIn_0 : UInt<8>
    input io_defVecSigIn_1 : UInt<8>
    input io_defVecSigIn_2 : UInt<8>
    input io_defVecSigIn_3 : UInt<8>
    input io_defVecSigIn_4 : UInt<8>
    input io_defVecSigIn_5 : UInt<8>
    output io_defVecSigOut : UInt<8>
    output io_regVecOut_0 : UInt<3>
    output io_regVecOut_1 : UInt<3>
    output io_regVecOut_2 : UInt<3>
    output io_resetRegFileOut : UInt<32>

    node _io_array_T = bits(io_idx, 1, 0)
    node v_0 = UInt<4>("h1") @[BundleVec.scala 52:15 56:8]
    node _GEN_0 = validif(eq(UInt<1>("h0"), _io_array_T), v_0) @[BundleVec.scala 64:{12,12}]
    node v_1 = UInt<4>("h3") @[BundleVec.scala 52:15 57:8]
    node _GEN_1 = mux(eq(UInt<1>("h1"), _io_array_T), v_1, _GEN_0) @[BundleVec.scala 64:{12,12}]
    node v_2 = UInt<4>("h5") @[BundleVec.scala 52:15 58:8]
    node _GEN_2 = mux(eq(UInt<2>("h2"), _io_array_T), v_2, _GEN_1) @[BundleVec.scala 64:{12,12}]
    reg regVec_0 : UInt<8>, clock with :
      reset => (UInt<1>("h0"), regVec_0) @[BundleVec.scala 71:19]
    reg regVec_1 : UInt<8>, clock with :
      reset => (UInt<1>("h0"), regVec_1) @[BundleVec.scala 71:19]
    reg regVec_2 : UInt<8>, clock with :
      reset => (UInt<1>("h0"), regVec_2) @[BundleVec.scala 71:19]
    node _regVec_io_wrIdx = io_din @[BundleVec.scala 74:{17,17}]
    node _GEN_3 = mux(eq(UInt<1>("h0"), io_wrIdx), _regVec_io_wrIdx, regVec_0) @[BundleVec.scala 74:{17,17} 71:19]
    node _GEN_4 = mux(eq(UInt<1>("h1"), io_wrIdx), _regVec_io_wrIdx, regVec_1) @[BundleVec.scala 74:{17,17} 71:19]
    node _GEN_5 = mux(eq(UInt<2>("h2"), io_wrIdx), _regVec_io_wrIdx, regVec_2) @[BundleVec.scala 74:{17,17} 71:19]
    node _GEN_6 = validif(eq(UInt<1>("h0"), io_rdIdx), regVec_0) @[BundleVec.scala 76:{11,11}]
    node _GEN_7 = mux(eq(UInt<1>("h1"), io_rdIdx), regVec_1, _GEN_6) @[BundleVec.scala 76:{11,11}]
    node _GEN_8 = mux(eq(UInt<2>("h2"), io_rdIdx), regVec_2, _GEN_7) @[BundleVec.scala 76:{11,11}]
    node vec_0 = UInt<8>("h0") @[BundleVec.scala 84:17 85:10]
    node _GEN_9 = validif(eq(UInt<1>("h0"), io_selMux), vec_0) @[BundleVec.scala 90:{13,13}]
    node vec_1 = UInt<8>("hb") @[BundleVec.scala 84:17 86:10]
    node _GEN_10 = mux(eq(UInt<1>("h1"), io_selMux), vec_1, _GEN_9) @[BundleVec.scala 90:{13,13}]
    node vec_2 = UInt<8>("h16") @[BundleVec.scala 84:17 87:10]
    node _GEN_11 = mux(eq(UInt<2>("h2"), io_selMux), vec_2, _GEN_10) @[BundleVec.scala 90:{13,13}]
    reg registerFile_0 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_0) @[BundleVec.scala 95:25]
    reg registerFile_1 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_1) @[BundleVec.scala 95:25]
    reg registerFile_2 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_2) @[BundleVec.scala 95:25]
    reg registerFile_3 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_3) @[BundleVec.scala 95:25]
    reg registerFile_4 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_4) @[BundleVec.scala 95:25]
    reg registerFile_5 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_5) @[BundleVec.scala 95:25]
    reg registerFile_6 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_6) @[BundleVec.scala 95:25]
    reg registerFile_7 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_7) @[BundleVec.scala 95:25]
    reg registerFile_8 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_8) @[BundleVec.scala 95:25]
    reg registerFile_9 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_9) @[BundleVec.scala 95:25]
    reg registerFile_10 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_10) @[BundleVec.scala 95:25]
    reg registerFile_11 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_11) @[BundleVec.scala 95:25]
    reg registerFile_12 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_12) @[BundleVec.scala 95:25]
    reg registerFile_13 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_13) @[BundleVec.scala 95:25]
    reg registerFile_14 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_14) @[BundleVec.scala 95:25]
    reg registerFile_15 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_15) @[BundleVec.scala 95:25]
    reg registerFile_16 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_16) @[BundleVec.scala 95:25]
    reg registerFile_17 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_17) @[BundleVec.scala 95:25]
    reg registerFile_18 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_18) @[BundleVec.scala 95:25]
    reg registerFile_19 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_19) @[BundleVec.scala 95:25]
    reg registerFile_20 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_20) @[BundleVec.scala 95:25]
    reg registerFile_21 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_21) @[BundleVec.scala 95:25]
    reg registerFile_22 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_22) @[BundleVec.scala 95:25]
    reg registerFile_23 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_23) @[BundleVec.scala 95:25]
    reg registerFile_24 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_24) @[BundleVec.scala 95:25]
    reg registerFile_25 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_25) @[BundleVec.scala 95:25]
    reg registerFile_26 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_26) @[BundleVec.scala 95:25]
    reg registerFile_27 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_27) @[BundleVec.scala 95:25]
    reg registerFile_28 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_28) @[BundleVec.scala 95:25]
    reg registerFile_29 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_29) @[BundleVec.scala 95:25]
    reg registerFile_30 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_30) @[BundleVec.scala 95:25]
    reg registerFile_31 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), registerFile_31) @[BundleVec.scala 95:25]
    reg channelReg_data : UInt<32>, clock with :
      reset => (UInt<1>("h0"), channelReg_data) @[BundleVec.scala 137:27]
    reg channelReg_valid : UInt<1>, clock with :
      reset => (UInt<1>("h0"), channelReg_valid) @[BundleVec.scala 137:27]
    node _GEN_12 = mux(io_selVecCond, UInt<3>("h4"), UInt<3>("h1")) @[BundleVec.scala 152:15 153:15 151:23]
    node _GEN_13 = mux(io_selVecCond, UInt<3>("h5"), UInt<2>("h2")) @[BundleVec.scala 152:15 154:15 151:23]
    node _GEN_14 = mux(io_selVecCond, UInt<3>("h6"), UInt<2>("h3")) @[BundleVec.scala 152:15 155:15 151:23]
    node _vecOut_T = bits(io_selVec, 1, 0)
    node defVec_0 = _GEN_12 @[BundleVec.scala 151:23]
    node _GEN_15 = validif(eq(UInt<1>("h0"), _vecOut_T), defVec_0) @[BundleVec.scala 159:{16,16}]
    node defVec_1 = _GEN_13 @[BundleVec.scala 151:23]
    node _GEN_16 = mux(eq(UInt<1>("h1"), _vecOut_T), defVec_1, _GEN_15) @[BundleVec.scala 159:{16,16}]
    node defVec_2 = _GEN_14 @[BundleVec.scala 151:23]
    node _GEN_17 = mux(eq(UInt<2>("h2"), _vecOut_T), defVec_2, _GEN_16) @[BundleVec.scala 159:{16,16}]
    node _vecOutSig_T = bits(io_selVec, 1, 0)
    node defVecSig_0 = io_defVecSigIn_0 @[BundleVec.scala 166:{26,26}]
    node _GEN_18 = validif(eq(UInt<1>("h0"), _vecOutSig_T), defVecSig_0) @[BundleVec.scala 170:{19,19}]
    node defVecSig_1 = io_defVecSigIn_1 @[BundleVec.scala 166:{26,26}]
    node _GEN_19 = mux(eq(UInt<1>("h1"), _vecOutSig_T), defVecSig_1, _GEN_18) @[BundleVec.scala 170:{19,19}]
    node defVecSig_2 = io_defVecSigIn_2 @[BundleVec.scala 166:{26,26}]
    node _GEN_20 = mux(eq(UInt<2>("h2"), _vecOutSig_T), defVecSig_2, _GEN_19) @[BundleVec.scala 170:{19,19}]
    reg initReg_0 : UInt<3>, clock with :
      reset => (UInt<1>("h0"), initReg_0) @[BundleVec.scala 173:24]
    reg initReg_1 : UInt<3>, clock with :
      reset => (UInt<1>("h0"), initReg_1) @[BundleVec.scala 173:24]
    reg initReg_2 : UInt<3>, clock with :
      reset => (UInt<1>("h0"), initReg_2) @[BundleVec.scala 173:24]
    node _resetVal_T = bits(io_selVec, 1, 0)
    reg resetRegFile_0 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_0) @[BundleVec.scala 183:29]
    reg resetRegFile_1 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_1) @[BundleVec.scala 183:29]
    reg resetRegFile_2 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_2) @[BundleVec.scala 183:29]
    reg resetRegFile_3 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_3) @[BundleVec.scala 183:29]
    reg resetRegFile_4 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_4) @[BundleVec.scala 183:29]
    reg resetRegFile_5 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_5) @[BundleVec.scala 183:29]
    reg resetRegFile_6 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_6) @[BundleVec.scala 183:29]
    reg resetRegFile_7 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_7) @[BundleVec.scala 183:29]
    reg resetRegFile_8 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_8) @[BundleVec.scala 183:29]
    reg resetRegFile_9 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_9) @[BundleVec.scala 183:29]
    reg resetRegFile_10 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_10) @[BundleVec.scala 183:29]
    reg resetRegFile_11 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_11) @[BundleVec.scala 183:29]
    reg resetRegFile_12 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_12) @[BundleVec.scala 183:29]
    reg resetRegFile_13 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_13) @[BundleVec.scala 183:29]
    reg resetRegFile_14 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_14) @[BundleVec.scala 183:29]
    reg resetRegFile_15 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_15) @[BundleVec.scala 183:29]
    reg resetRegFile_16 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_16) @[BundleVec.scala 183:29]
    reg resetRegFile_17 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_17) @[BundleVec.scala 183:29]
    reg resetRegFile_18 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_18) @[BundleVec.scala 183:29]
    reg resetRegFile_19 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_19) @[BundleVec.scala 183:29]
    reg resetRegFile_20 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_20) @[BundleVec.scala 183:29]
    reg resetRegFile_21 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_21) @[BundleVec.scala 183:29]
    reg resetRegFile_22 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_22) @[BundleVec.scala 183:29]
    reg resetRegFile_23 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_23) @[BundleVec.scala 183:29]
    reg resetRegFile_24 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_24) @[BundleVec.scala 183:29]
    reg resetRegFile_25 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_25) @[BundleVec.scala 183:29]
    reg resetRegFile_26 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_26) @[BundleVec.scala 183:29]
    reg resetRegFile_27 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_27) @[BundleVec.scala 183:29]
    reg resetRegFile_28 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_28) @[BundleVec.scala 183:29]
    reg resetRegFile_29 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_29) @[BundleVec.scala 183:29]
    reg resetRegFile_30 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_30) @[BundleVec.scala 183:29]
    reg resetRegFile_31 : UInt<32>, clock with :
      reset => (UInt<1>("h0"), resetRegFile_31) @[BundleVec.scala 183:29]
    node _GEN_21 = validif(eq(UInt<1>("h0"), io_selVec), resetRegFile_0) @[BundleVec.scala 187:{22,22}]
    node _GEN_22 = mux(eq(UInt<1>("h1"), io_selVec), resetRegFile_1, _GEN_21) @[BundleVec.scala 187:{22,22}]
    node _GEN_23 = mux(eq(UInt<2>("h2"), io_selVec), resetRegFile_2, _GEN_22) @[BundleVec.scala 187:{22,22}]
    node _GEN_24 = mux(eq(UInt<2>("h3"), io_selVec), resetRegFile_3, _GEN_23) @[BundleVec.scala 187:{22,22}]
    node _GEN_25 = mux(eq(UInt<3>("h4"), io_selVec), resetRegFile_4, _GEN_24) @[BundleVec.scala 187:{22,22}]
    node _GEN_26 = mux(eq(UInt<3>("h5"), io_selVec), resetRegFile_5, _GEN_25) @[BundleVec.scala 187:{22,22}]
    node _GEN_27 = mux(eq(UInt<3>("h6"), io_selVec), resetRegFile_6, _GEN_26) @[BundleVec.scala 187:{22,22}]
    node _GEN_28 = mux(eq(UInt<3>("h7"), io_selVec), resetRegFile_7, _GEN_27) @[BundleVec.scala 187:{22,22}]
    node _GEN_29 = mux(eq(UInt<4>("h8"), io_selVec), resetRegFile_8, _GEN_28) @[BundleVec.scala 187:{22,22}]
    node _GEN_30 = mux(eq(UInt<4>("h9"), io_selVec), resetRegFile_9, _GEN_29) @[BundleVec.scala 187:{22,22}]
    node _GEN_31 = mux(eq(UInt<4>("ha"), io_selVec), resetRegFile_10, _GEN_30) @[BundleVec.scala 187:{22,22}]
    node _GEN_32 = mux(eq(UInt<4>("hb"), io_selVec), resetRegFile_11, _GEN_31) @[BundleVec.scala 187:{22,22}]
    node _GEN_33 = mux(eq(UInt<4>("hc"), io_selVec), resetRegFile_12, _GEN_32) @[BundleVec.scala 187:{22,22}]
    node _GEN_34 = mux(eq(UInt<4>("hd"), io_selVec), resetRegFile_13, _GEN_33) @[BundleVec.scala 187:{22,22}]
    node _GEN_35 = mux(eq(UInt<4>("he"), io_selVec), resetRegFile_14, _GEN_34) @[BundleVec.scala 187:{22,22}]
    node _GEN_36 = mux(eq(UInt<4>("hf"), io_selVec), resetRegFile_15, _GEN_35) @[BundleVec.scala 187:{22,22}]
    node _GEN_37 = mux(eq(UInt<5>("h10"), io_selVec), resetRegFile_16, _GEN_36) @[BundleVec.scala 187:{22,22}]
    node _GEN_38 = mux(eq(UInt<5>("h11"), io_selVec), resetRegFile_17, _GEN_37) @[BundleVec.scala 187:{22,22}]
    node _GEN_39 = mux(eq(UInt<5>("h12"), io_selVec), resetRegFile_18, _GEN_38) @[BundleVec.scala 187:{22,22}]
    node _GEN_40 = mux(eq(UInt<5>("h13"), io_selVec), resetRegFile_19, _GEN_39) @[BundleVec.scala 187:{22,22}]
    node _GEN_41 = mux(eq(UInt<5>("h14"), io_selVec), resetRegFile_20, _GEN_40) @[BundleVec.scala 187:{22,22}]
    node _GEN_42 = mux(eq(UInt<5>("h15"), io_selVec), resetRegFile_21, _GEN_41) @[BundleVec.scala 187:{22,22}]
    node _GEN_43 = mux(eq(UInt<5>("h16"), io_selVec), resetRegFile_22, _GEN_42) @[BundleVec.scala 187:{22,22}]
    node _GEN_44 = mux(eq(UInt<5>("h17"), io_selVec), resetRegFile_23, _GEN_43) @[BundleVec.scala 187:{22,22}]
    node _GEN_45 = mux(eq(UInt<5>("h18"), io_selVec), resetRegFile_24, _GEN_44) @[BundleVec.scala 187:{22,22}]
    node _GEN_46 = mux(eq(UInt<5>("h19"), io_selVec), resetRegFile_25, _GEN_45) @[BundleVec.scala 187:{22,22}]
    node _GEN_47 = mux(eq(UInt<5>("h1a"), io_selVec), resetRegFile_26, _GEN_46) @[BundleVec.scala 187:{22,22}]
    node _GEN_48 = mux(eq(UInt<5>("h1b"), io_selVec), resetRegFile_27, _GEN_47) @[BundleVec.scala 187:{22,22}]
    node _GEN_49 = mux(eq(UInt<5>("h1c"), io_selVec), resetRegFile_28, _GEN_48) @[BundleVec.scala 187:{22,22}]
    node _GEN_50 = mux(eq(UInt<5>("h1d"), io_selVec), resetRegFile_29, _GEN_49) @[BundleVec.scala 187:{22,22}]
    node _GEN_51 = mux(eq(UInt<5>("h1e"), io_selVec), resetRegFile_30, _GEN_50) @[BundleVec.scala 187:{22,22}]
    node _GEN_52 = mux(eq(UInt<5>("h1f"), io_selVec), resetRegFile_31, _GEN_51) @[BundleVec.scala 187:{22,22}]
    node ch_data = UInt<32>("h7b") @[BundleVec.scala 40:16 41:11]
    node ch_valid = UInt<1>("h1") @[BundleVec.scala 40:16 42:12]
    node _v_io_array_T = _GEN_2 @[BundleVec.scala 64:12]
    node _regVec_io_rdIdx = _GEN_8 @[BundleVec.scala 76:11]
    node _vec_io_selMux = _GEN_11 @[BundleVec.scala 90:13]
    node vecBundle_0_data = ch_data @[BundleVec.scala 108:23 112:18]
    node vecBundle_0_valid = ch_valid @[BundleVec.scala 108:23 112:18]
    node vecBundle_1_data = ch_data @[BundleVec.scala 108:23 112:18]
    node vecBundle_1_valid = ch_valid @[BundleVec.scala 108:23 112:18]
    node vecBundle_2_data = ch_data @[BundleVec.scala 108:23 112:18]
    node vecBundle_2_valid = ch_valid @[BundleVec.scala 108:23 112:18]
    node vecBundle_3_data = ch_data @[BundleVec.scala 108:23 112:18]
    node vecBundle_3_valid = ch_valid @[BundleVec.scala 108:23 112:18]
    node vecBundle_4_data = ch_data @[BundleVec.scala 108:23 112:18]
    node vecBundle_4_valid = ch_valid @[BundleVec.scala 108:23 112:18]
    node vecBundle_5_data = ch_data @[BundleVec.scala 108:23 112:18]
    node vecBundle_5_valid = ch_valid @[BundleVec.scala 108:23 112:18]
    node vecBundle_6_data = ch_data @[BundleVec.scala 108:23 112:18]
    node vecBundle_6_valid = ch_valid @[BundleVec.scala 108:23 112:18]
    node vecBundle_7_data = ch_data @[BundleVec.scala 108:23 112:18]
    node vecBundle_7_valid = ch_valid @[BundleVec.scala 108:23 112:18]
    node bv_field = UInt<8>("hd") @[BundleVec.scala 123:16 124:12]
    node bv_vector_0 = UInt<8>("h3") @[BundleVec.scala 123:16 126:18]
    node bv_vector_1 = UInt<8>("h3") @[BundleVec.scala 123:16 126:18]
    node bv_vector_2 = UInt<8>("h3") @[BundleVec.scala 123:16 126:18]
    node bv_vector_3 = UInt<8>("h3") @[BundleVec.scala 123:16 126:18]
    node initVal_data = UInt<32>("h0") @[BundleVec.scala 132:21 134:16]
    node initVal_valid = UInt<1>("h0") @[BundleVec.scala 132:21 135:17]
    node _defVec_vecOut_T = _GEN_17 @[BundleVec.scala 159:16]
    node _defVecSig_vecOutSig_T = _GEN_20 @[BundleVec.scala 170:19]
    node _initReg_WIRE_0 = UInt<3>("h0") @[BundleVec.scala 173:{32,32}]
    node _initReg_WIRE_1 = UInt<3>("h1") @[BundleVec.scala 173:{32,32}]
    node _initReg_WIRE_2 = UInt<3>("h2") @[BundleVec.scala 173:{32,32}]
    node _resetRegFile_WIRE_0 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_1 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_2 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_3 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_4 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_5 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_6 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_7 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_8 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_9 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_10 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_11 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_12 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_13 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_14 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_15 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_16 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_17 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_18 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_19 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_20 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_21 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_22 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_23 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_24 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_25 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_26 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_27 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_28 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_29 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_30 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_WIRE_31 = UInt<32>("h0") @[BundleVec.scala 183:{37,37}]
    node _resetRegFile_io_selVec = _GEN_52 @[BundleVec.scala 187:22]
    io_chan_data <= ch_data @[BundleVec.scala 65:11]
    io_chan_valid <= ch_valid @[BundleVec.scala 65:11]
    io_chan2_data <= vecBundle_1_data @[BundleVec.scala 114:12]
    io_chan2_valid <= vecBundle_1_valid @[BundleVec.scala 114:12]
    io_array <= _v_io_array_T @[BundleVec.scala 64:12]
    io_dOut <= registerFile_1 @[BundleVec.scala 105:11]
    io_bvOut <= bv_field @[BundleVec.scala 129:12]
    io_chreg_data <= channelReg_data @[BundleVec.scala 143:12]
    io_chreg_valid <= channelReg_valid @[BundleVec.scala 143:12]
    io_dout <= _regVec_io_rdIdx @[BundleVec.scala 76:11]
    io_muxOut <= _vec_io_selMux @[BundleVec.scala 90:13]
    io_defVecOut <= _defVec_vecOut_T @[BundleVec.scala 159:16]
    io_defVecSigOut <= _defVecSig_vecOutSig_T @[BundleVec.scala 170:19]
    io_regVecOut_0 <= initReg_0 @[BundleVec.scala 180:16]
    io_regVecOut_1 <= initReg_1 @[BundleVec.scala 180:16]
    io_regVecOut_2 <= initReg_2 @[BundleVec.scala 180:16]
    io_resetRegFileOut <= _resetRegFile_io_selVec @[BundleVec.scala 187:22]
    regVec_0 <= _GEN_3
    regVec_1 <= _GEN_4
    regVec_2 <= _GEN_5
    registerFile_0 <= registerFile_0 @[BundleVec.scala 95:25]
    registerFile_1 <= io_dIn @[BundleVec.scala 101:23]
    registerFile_2 <= registerFile_2 @[BundleVec.scala 95:25]
    registerFile_3 <= registerFile_3 @[BundleVec.scala 95:25]
    registerFile_4 <= registerFile_4 @[BundleVec.scala 95:25]
    registerFile_5 <= registerFile_5 @[BundleVec.scala 95:25]
    registerFile_6 <= registerFile_6 @[BundleVec.scala 95:25]
    registerFile_7 <= registerFile_7 @[BundleVec.scala 95:25]
    registerFile_8 <= registerFile_8 @[BundleVec.scala 95:25]
    registerFile_9 <= registerFile_9 @[BundleVec.scala 95:25]
    registerFile_10 <= registerFile_10 @[BundleVec.scala 95:25]
    registerFile_11 <= registerFile_11 @[BundleVec.scala 95:25]
    registerFile_12 <= registerFile_12 @[BundleVec.scala 95:25]
    registerFile_13 <= registerFile_13 @[BundleVec.scala 95:25]
    registerFile_14 <= registerFile_14 @[BundleVec.scala 95:25]
    registerFile_15 <= registerFile_15 @[BundleVec.scala 95:25]
    registerFile_16 <= registerFile_16 @[BundleVec.scala 95:25]
    registerFile_17 <= registerFile_17 @[BundleVec.scala 95:25]
    registerFile_18 <= registerFile_18 @[BundleVec.scala 95:25]
    registerFile_19 <= registerFile_19 @[BundleVec.scala 95:25]
    registerFile_20 <= registerFile_20 @[BundleVec.scala 95:25]
    registerFile_21 <= registerFile_21 @[BundleVec.scala 95:25]
    registerFile_22 <= registerFile_22 @[BundleVec.scala 95:25]
    registerFile_23 <= registerFile_23 @[BundleVec.scala 95:25]
    registerFile_24 <= registerFile_24 @[BundleVec.scala 95:25]
    registerFile_25 <= registerFile_25 @[BundleVec.scala 95:25]
    registerFile_26 <= registerFile_26 @[BundleVec.scala 95:25]
    registerFile_27 <= registerFile_27 @[BundleVec.scala 95:25]
    registerFile_28 <= registerFile_28 @[BundleVec.scala 95:25]
    registerFile_29 <= registerFile_29 @[BundleVec.scala 95:25]
    registerFile_30 <= registerFile_30 @[BundleVec.scala 95:25]
    registerFile_31 <= registerFile_31 @[BundleVec.scala 95:25]
    channelReg_data <= mux(reset1, initVal_data, UInt<1>("h1")) @[BundleVec.scala 137:{27,27} 140:19]
    channelReg_valid <= mux(reset1, initVal_valid, UInt<1>("h1")) @[BundleVec.scala 137:{27,27} 141:20]
    initReg_0 <= bits(mux(reset1, _initReg_WIRE_0, io_defVecSigIn_0), 2, 0) @[BundleVec.scala 173:{24,24} 175:14]
    initReg_1 <= bits(mux(reset1, _initReg_WIRE_1, io_defVecSigIn_1), 2, 0) @[BundleVec.scala 173:{24,24} 176:14]
    initReg_2 <= bits(mux(reset1, _initReg_WIRE_2, io_defVecSigIn_2), 2, 0) @[BundleVec.scala 173:{24,24} 177:14]
    resetRegFile_0 <= mux(reset1, _resetRegFile_WIRE_0, resetRegFile_0) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_1 <= mux(reset1, _resetRegFile_WIRE_1, resetRegFile_1) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_2 <= mux(reset1, _resetRegFile_WIRE_2, resetRegFile_2) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_3 <= mux(reset1, _resetRegFile_WIRE_3, resetRegFile_3) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_4 <= mux(reset1, _resetRegFile_WIRE_4, resetRegFile_4) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_5 <= mux(reset1, _resetRegFile_WIRE_5, resetRegFile_5) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_6 <= mux(reset1, _resetRegFile_WIRE_6, resetRegFile_6) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_7 <= mux(reset1, _resetRegFile_WIRE_7, resetRegFile_7) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_8 <= mux(reset1, _resetRegFile_WIRE_8, resetRegFile_8) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_9 <= mux(reset1, _resetRegFile_WIRE_9, resetRegFile_9) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_10 <= mux(reset1, _resetRegFile_WIRE_10, resetRegFile_10) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_11 <= mux(reset1, _resetRegFile_WIRE_11, resetRegFile_11) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_12 <= mux(reset1, _resetRegFile_WIRE_12, resetRegFile_12) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_13 <= mux(reset1, _resetRegFile_WIRE_13, resetRegFile_13) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_14 <= mux(reset1, _resetRegFile_WIRE_14, resetRegFile_14) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_15 <= mux(reset1, _resetRegFile_WIRE_15, resetRegFile_15) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_16 <= mux(reset1, _resetRegFile_WIRE_16, resetRegFile_16) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_17 <= mux(reset1, _resetRegFile_WIRE_17, resetRegFile_17) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_18 <= mux(reset1, _resetRegFile_WIRE_18, resetRegFile_18) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_19 <= mux(reset1, _resetRegFile_WIRE_19, resetRegFile_19) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_20 <= mux(reset1, _resetRegFile_WIRE_20, resetRegFile_20) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_21 <= mux(reset1, _resetRegFile_WIRE_21, resetRegFile_21) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_22 <= mux(reset1, _resetRegFile_WIRE_22, resetRegFile_22) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_23 <= mux(reset1, _resetRegFile_WIRE_23, resetRegFile_23) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_24 <= mux(reset1, _resetRegFile_WIRE_24, resetRegFile_24) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_25 <= mux(reset1, _resetRegFile_WIRE_25, resetRegFile_25) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_26 <= mux(reset1, _resetRegFile_WIRE_26, resetRegFile_26) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_27 <= mux(reset1, _resetRegFile_WIRE_27, resetRegFile_27) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_28 <= mux(reset1, _resetRegFile_WIRE_28, resetRegFile_28) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_29 <= mux(reset1, _resetRegFile_WIRE_29, resetRegFile_29) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_30 <= mux(reset1, _resetRegFile_WIRE_30, resetRegFile_30) @[BundleVec.scala 183:{29,29,29}]
    resetRegFile_31 <= mux(reset1, _resetRegFile_WIRE_31, resetRegFile_31) @[BundleVec.scala 183:{29,29,29}]
