circuit ArbiterSimpleTree :
  module ArbiterSimpleTree :
    input clock : Clock
    input reset1 : UInt<1>
    output io_in_0_ready : UInt<1>
    input io_in_0_valid : UInt<1>
    input io_in_0_bits : UInt<8>
    output io_in_1_ready : UInt<1>
    input io_in_1_valid : UInt<1>
    input io_in_1_bits : UInt<8>
    output io_in_2_ready : UInt<1>
    input io_in_2_valid : UInt<1>
    input io_in_2_bits : UInt<8>
    output io_in_3_ready : UInt<1>
    input io_in_3_valid : UInt<1>
    input io_in_3_bits : UInt<8>
    output io_in_4_ready : UInt<1>
    input io_in_4_valid : UInt<1>
    input io_in_4_bits : UInt<8>
    output io_in_5_ready : UInt<1>
    input io_in_5_valid : UInt<1>
    input io_in_5_bits : UInt<8>
    output io_in_6_ready : UInt<1>
    input io_in_6_valid : UInt<1>
    input io_in_6_bits : UInt<8>
    input io_out_ready : UInt<1>
    output io_out_valid : UInt<1>
    output io_out_bits : UInt<8>

    reg io_out_regData : UInt<8>, clock with :
      reset => (UInt<1>("h0"), io_out_regData) @[ArbiterTree.scala 79:22]
    reg io_out_regEmpty : UInt<1>, clock with :
      reset => (UInt<1>("h0"), io_out_regEmpty) @[ArbiterTree.scala 80:27]
    reg io_out_regReadyA : UInt<1>, clock with :
      reset => (UInt<1>("h0"), io_out_regReadyA) @[ArbiterTree.scala 81:28]
    reg io_out_regReadyB : UInt<1>, clock with :
      reset => (UInt<1>("h0"), io_out_regReadyB) @[ArbiterTree.scala 82:28]
    node _io_out_T = and(io_in_1_valid, io_out_regEmpty) @[ArbiterTree.scala 86:19]
    node _io_out_T_1 = eq(io_out_regReadyB, UInt<1>("h0")) @[ArbiterTree.scala 86:32]
    node _io_out_T_2 = and(_io_out_T, _io_out_T_1) @[ArbiterTree.scala 86:30]
    node _io_out_T_3 = and(io_in_2_valid, io_out_regEmpty) @[ArbiterTree.scala 88:26]
    node _io_out_T_4 = eq(io_out_regReadyA, UInt<1>("h0")) @[ArbiterTree.scala 88:39]
    node _io_out_T_5 = and(_io_out_T_3, _io_out_T_4) @[ArbiterTree.scala 88:37]
    node _GEN_0 = mux(_io_out_T_5, UInt<1>("h1"), io_out_regReadyB) @[ArbiterTree.scala 88:51 89:17 82:28]
    node _GEN_1 = mux(_io_out_T_2, UInt<1>("h1"), io_out_regReadyA) @[ArbiterTree.scala 86:44 87:17 81:28]
    node _GEN_2 = mux(_io_out_T_2, io_out_regReadyB, _GEN_0) @[ArbiterTree.scala 82:28 86:44]
    node _GEN_3 = mux(io_out_regReadyA, io_in_1_bits, io_out_regData) @[ArbiterTree.scala 94:22 95:15 79:22]
    node _GEN_4 = mux(io_out_regReadyA, UInt<1>("h0"), io_out_regEmpty) @[ArbiterTree.scala 94:22 96:16 80:27]
    node _GEN_5 = mux(io_out_regReadyA, UInt<1>("h0"), _GEN_1) @[ArbiterTree.scala 94:22 97:17]
    node _GEN_6 = mux(io_out_regReadyB, io_in_2_bits, _GEN_3) @[ArbiterTree.scala 100:15 99:22]
    node _GEN_7 = mux(io_out_regReadyB, UInt<1>("h0"), _GEN_4) @[ArbiterTree.scala 101:16 99:22]
    node _GEN_8 = mux(io_out_regReadyB, UInt<1>("h0"), _GEN_2) @[ArbiterTree.scala 102:17 99:22]
    node _io_out_out_valid_T = eq(io_out_regEmpty, UInt<1>("h0")) @[ArbiterTree.scala 105:18]
    reg io_out_regReadyB_3 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), io_out_regReadyB_3) @[ArbiterTree.scala 82:28]
    node io_out_out_ready = io_out_regReadyB_3 @[ArbiterTree.scala 84:19 92:13]
    node _GEN_9 = mux(io_out_out_ready, UInt<1>("h1"), _GEN_7) @[ArbiterTree.scala 106:22 107:16]
    reg io_out_regData_1 : UInt<8>, clock with :
      reset => (UInt<1>("h0"), io_out_regData_1) @[ArbiterTree.scala 79:22]
    reg io_out_regEmpty_1 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), io_out_regEmpty_1) @[ArbiterTree.scala 80:27]
    reg io_out_regReadyA_1 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), io_out_regReadyA_1) @[ArbiterTree.scala 81:28]
    reg io_out_regReadyB_1 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), io_out_regReadyB_1) @[ArbiterTree.scala 82:28]
    node _io_out_T_6 = and(io_in_3_valid, io_out_regEmpty_1) @[ArbiterTree.scala 86:19]
    node _io_out_T_7 = eq(io_out_regReadyB_1, UInt<1>("h0")) @[ArbiterTree.scala 86:32]
    node _io_out_T_8 = and(_io_out_T_6, _io_out_T_7) @[ArbiterTree.scala 86:30]
    node _io_out_T_9 = and(io_in_4_valid, io_out_regEmpty_1) @[ArbiterTree.scala 88:26]
    node _io_out_T_10 = eq(io_out_regReadyA_1, UInt<1>("h0")) @[ArbiterTree.scala 88:39]
    node _io_out_T_11 = and(_io_out_T_9, _io_out_T_10) @[ArbiterTree.scala 88:37]
    node _GEN_10 = mux(_io_out_T_11, UInt<1>("h1"), io_out_regReadyB_1) @[ArbiterTree.scala 88:51 89:17 82:28]
    node _GEN_11 = mux(_io_out_T_8, UInt<1>("h1"), io_out_regReadyA_1) @[ArbiterTree.scala 86:44 87:17 81:28]
    node _GEN_12 = mux(_io_out_T_8, io_out_regReadyB_1, _GEN_10) @[ArbiterTree.scala 82:28 86:44]
    node _GEN_13 = mux(io_out_regReadyA_1, io_in_3_bits, io_out_regData_1) @[ArbiterTree.scala 94:22 95:15 79:22]
    node _GEN_14 = mux(io_out_regReadyA_1, UInt<1>("h0"), io_out_regEmpty_1) @[ArbiterTree.scala 94:22 96:16 80:27]
    node _GEN_15 = mux(io_out_regReadyA_1, UInt<1>("h0"), _GEN_11) @[ArbiterTree.scala 94:22 97:17]
    node _GEN_16 = mux(io_out_regReadyB_1, io_in_4_bits, _GEN_13) @[ArbiterTree.scala 100:15 99:22]
    node _GEN_17 = mux(io_out_regReadyB_1, UInt<1>("h0"), _GEN_14) @[ArbiterTree.scala 101:16 99:22]
    node _GEN_18 = mux(io_out_regReadyB_1, UInt<1>("h0"), _GEN_12) @[ArbiterTree.scala 102:17 99:22]
    node _io_out_out_valid_T_1 = eq(io_out_regEmpty_1, UInt<1>("h0")) @[ArbiterTree.scala 105:18]
    reg io_out_regReadyA_4 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), io_out_regReadyA_4) @[ArbiterTree.scala 81:28]
    node io_out_out_1_ready = io_out_regReadyA_4 @[ArbiterTree.scala 84:19 91:13]
    node _GEN_19 = mux(io_out_out_1_ready, UInt<1>("h1"), _GEN_17) @[ArbiterTree.scala 106:22 107:16]
    reg io_out_regData_2 : UInt<8>, clock with :
      reset => (UInt<1>("h0"), io_out_regData_2) @[ArbiterTree.scala 79:22]
    reg io_out_regEmpty_2 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), io_out_regEmpty_2) @[ArbiterTree.scala 80:27]
    reg io_out_regReadyA_2 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), io_out_regReadyA_2) @[ArbiterTree.scala 81:28]
    reg io_out_regReadyB_2 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), io_out_regReadyB_2) @[ArbiterTree.scala 82:28]
    node _io_out_T_12 = and(io_in_5_valid, io_out_regEmpty_2) @[ArbiterTree.scala 86:19]
    node _io_out_T_13 = eq(io_out_regReadyB_2, UInt<1>("h0")) @[ArbiterTree.scala 86:32]
    node _io_out_T_14 = and(_io_out_T_12, _io_out_T_13) @[ArbiterTree.scala 86:30]
    node _io_out_T_15 = and(io_in_6_valid, io_out_regEmpty_2) @[ArbiterTree.scala 88:26]
    node _io_out_T_16 = eq(io_out_regReadyA_2, UInt<1>("h0")) @[ArbiterTree.scala 88:39]
    node _io_out_T_17 = and(_io_out_T_15, _io_out_T_16) @[ArbiterTree.scala 88:37]
    node _GEN_20 = mux(_io_out_T_17, UInt<1>("h1"), io_out_regReadyB_2) @[ArbiterTree.scala 88:51 89:17 82:28]
    node _GEN_21 = mux(_io_out_T_14, UInt<1>("h1"), io_out_regReadyA_2) @[ArbiterTree.scala 86:44 87:17 81:28]
    node _GEN_22 = mux(_io_out_T_14, io_out_regReadyB_2, _GEN_20) @[ArbiterTree.scala 82:28 86:44]
    node _GEN_23 = mux(io_out_regReadyA_2, io_in_5_bits, io_out_regData_2) @[ArbiterTree.scala 94:22 95:15 79:22]
    node _GEN_24 = mux(io_out_regReadyA_2, UInt<1>("h0"), io_out_regEmpty_2) @[ArbiterTree.scala 94:22 96:16 80:27]
    node _GEN_25 = mux(io_out_regReadyA_2, UInt<1>("h0"), _GEN_21) @[ArbiterTree.scala 94:22 97:17]
    node _GEN_26 = mux(io_out_regReadyB_2, io_in_6_bits, _GEN_23) @[ArbiterTree.scala 100:15 99:22]
    node _GEN_27 = mux(io_out_regReadyB_2, UInt<1>("h0"), _GEN_24) @[ArbiterTree.scala 101:16 99:22]
    node _GEN_28 = mux(io_out_regReadyB_2, UInt<1>("h0"), _GEN_22) @[ArbiterTree.scala 102:17 99:22]
    node _io_out_out_valid_T_2 = eq(io_out_regEmpty_2, UInt<1>("h0")) @[ArbiterTree.scala 105:18]
    reg io_out_regReadyB_4 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), io_out_regReadyB_4) @[ArbiterTree.scala 82:28]
    node io_out_out_2_ready = io_out_regReadyB_4 @[ArbiterTree.scala 84:19 92:13]
    node _GEN_29 = mux(io_out_out_2_ready, UInt<1>("h1"), _GEN_27) @[ArbiterTree.scala 106:22 107:16]
    reg io_out_regData_3 : UInt<8>, clock with :
      reset => (UInt<1>("h0"), io_out_regData_3) @[ArbiterTree.scala 79:22]
    reg io_out_regEmpty_3 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), io_out_regEmpty_3) @[ArbiterTree.scala 80:27]
    reg io_out_regReadyA_3 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), io_out_regReadyA_3) @[ArbiterTree.scala 81:28]
    node _io_out_T_18 = and(io_in_0_valid, io_out_regEmpty_3) @[ArbiterTree.scala 86:19]
    node _io_out_T_19 = eq(io_out_regReadyB_3, UInt<1>("h0")) @[ArbiterTree.scala 86:32]
    node _io_out_T_20 = and(_io_out_T_18, _io_out_T_19) @[ArbiterTree.scala 86:30]
    node io_out_out_valid = _io_out_out_valid_T @[ArbiterTree.scala 105:15 84:19]
    node _io_out_T_21 = and(io_out_out_valid, io_out_regEmpty_3) @[ArbiterTree.scala 88:26]
    node _io_out_T_22 = eq(io_out_regReadyA_3, UInt<1>("h0")) @[ArbiterTree.scala 88:39]
    node _io_out_T_23 = and(_io_out_T_21, _io_out_T_22) @[ArbiterTree.scala 88:37]
    node _GEN_30 = mux(_io_out_T_23, UInt<1>("h1"), io_out_regReadyB_3) @[ArbiterTree.scala 88:51 89:17 82:28]
    node _GEN_31 = mux(_io_out_T_20, UInt<1>("h1"), io_out_regReadyA_3) @[ArbiterTree.scala 86:44 87:17 81:28]
    node _GEN_32 = mux(_io_out_T_20, io_out_regReadyB_3, _GEN_30) @[ArbiterTree.scala 82:28 86:44]
    node _GEN_33 = mux(io_out_regReadyA_3, io_in_0_bits, io_out_regData_3) @[ArbiterTree.scala 94:22 95:15 79:22]
    node _GEN_34 = mux(io_out_regReadyA_3, UInt<1>("h0"), io_out_regEmpty_3) @[ArbiterTree.scala 94:22 96:16 80:27]
    node _GEN_35 = mux(io_out_regReadyA_3, UInt<1>("h0"), _GEN_31) @[ArbiterTree.scala 94:22 97:17]
    node io_out_out_bits = io_out_regData @[ArbiterTree.scala 110:14 84:19]
    node _GEN_36 = mux(io_out_regReadyB_3, io_out_out_bits, _GEN_33) @[ArbiterTree.scala 100:15 99:22]
    node _GEN_37 = mux(io_out_regReadyB_3, UInt<1>("h0"), _GEN_34) @[ArbiterTree.scala 101:16 99:22]
    node _GEN_38 = mux(io_out_regReadyB_3, UInt<1>("h0"), _GEN_32) @[ArbiterTree.scala 102:17 99:22]
    node _io_out_out_valid_T_3 = eq(io_out_regEmpty_3, UInt<1>("h0")) @[ArbiterTree.scala 105:18]
    reg io_out_regReadyA_5 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), io_out_regReadyA_5) @[ArbiterTree.scala 81:28]
    node io_out_out_3_ready = io_out_regReadyA_5 @[ArbiterTree.scala 84:19 91:13]
    node _GEN_39 = mux(io_out_out_3_ready, UInt<1>("h1"), _GEN_37) @[ArbiterTree.scala 106:22 107:16]
    reg io_out_regData_4 : UInt<8>, clock with :
      reset => (UInt<1>("h0"), io_out_regData_4) @[ArbiterTree.scala 79:22]
    reg io_out_regEmpty_4 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), io_out_regEmpty_4) @[ArbiterTree.scala 80:27]
    node io_out_out_1_valid = _io_out_out_valid_T_1 @[ArbiterTree.scala 105:15 84:19]
    node _io_out_T_24 = and(io_out_out_1_valid, io_out_regEmpty_4) @[ArbiterTree.scala 86:19]
    node _io_out_T_25 = eq(io_out_regReadyB_4, UInt<1>("h0")) @[ArbiterTree.scala 86:32]
    node _io_out_T_26 = and(_io_out_T_24, _io_out_T_25) @[ArbiterTree.scala 86:30]
    node io_out_out_2_valid = _io_out_out_valid_T_2 @[ArbiterTree.scala 105:15 84:19]
    node _io_out_T_27 = and(io_out_out_2_valid, io_out_regEmpty_4) @[ArbiterTree.scala 88:26]
    node _io_out_T_28 = eq(io_out_regReadyA_4, UInt<1>("h0")) @[ArbiterTree.scala 88:39]
    node _io_out_T_29 = and(_io_out_T_27, _io_out_T_28) @[ArbiterTree.scala 88:37]
    node _GEN_40 = mux(_io_out_T_29, UInt<1>("h1"), io_out_regReadyB_4) @[ArbiterTree.scala 88:51 89:17 82:28]
    node _GEN_41 = mux(_io_out_T_26, UInt<1>("h1"), io_out_regReadyA_4) @[ArbiterTree.scala 86:44 87:17 81:28]
    node _GEN_42 = mux(_io_out_T_26, io_out_regReadyB_4, _GEN_40) @[ArbiterTree.scala 82:28 86:44]
    node io_out_out_1_bits = io_out_regData_1 @[ArbiterTree.scala 110:14 84:19]
    node _GEN_43 = mux(io_out_regReadyA_4, io_out_out_1_bits, io_out_regData_4) @[ArbiterTree.scala 94:22 95:15 79:22]
    node _GEN_44 = mux(io_out_regReadyA_4, UInt<1>("h0"), io_out_regEmpty_4) @[ArbiterTree.scala 94:22 96:16 80:27]
    node _GEN_45 = mux(io_out_regReadyA_4, UInt<1>("h0"), _GEN_41) @[ArbiterTree.scala 94:22 97:17]
    node io_out_out_2_bits = io_out_regData_2 @[ArbiterTree.scala 110:14 84:19]
    node _GEN_46 = mux(io_out_regReadyB_4, io_out_out_2_bits, _GEN_43) @[ArbiterTree.scala 100:15 99:22]
    node _GEN_47 = mux(io_out_regReadyB_4, UInt<1>("h0"), _GEN_44) @[ArbiterTree.scala 101:16 99:22]
    node _GEN_48 = mux(io_out_regReadyB_4, UInt<1>("h0"), _GEN_42) @[ArbiterTree.scala 102:17 99:22]
    node _io_out_out_valid_T_4 = eq(io_out_regEmpty_4, UInt<1>("h0")) @[ArbiterTree.scala 105:18]
    reg io_out_regReadyB_5 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), io_out_regReadyB_5) @[ArbiterTree.scala 82:28]
    node io_out_out_4_ready = io_out_regReadyB_5 @[ArbiterTree.scala 84:19 92:13]
    node _GEN_49 = mux(io_out_out_4_ready, UInt<1>("h1"), _GEN_47) @[ArbiterTree.scala 106:22 107:16]
    reg io_out_regData_5 : UInt<8>, clock with :
      reset => (UInt<1>("h0"), io_out_regData_5) @[ArbiterTree.scala 79:22]
    reg io_out_regEmpty_5 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), io_out_regEmpty_5) @[ArbiterTree.scala 80:27]
    node io_out_out_3_valid = _io_out_out_valid_T_3 @[ArbiterTree.scala 105:15 84:19]
    node _io_out_T_30 = and(io_out_out_3_valid, io_out_regEmpty_5) @[ArbiterTree.scala 86:19]
    node _io_out_T_31 = eq(io_out_regReadyB_5, UInt<1>("h0")) @[ArbiterTree.scala 86:32]
    node _io_out_T_32 = and(_io_out_T_30, _io_out_T_31) @[ArbiterTree.scala 86:30]
    node io_out_out_4_valid = _io_out_out_valid_T_4 @[ArbiterTree.scala 105:15 84:19]
    node _io_out_T_33 = and(io_out_out_4_valid, io_out_regEmpty_5) @[ArbiterTree.scala 88:26]
    node _io_out_T_34 = eq(io_out_regReadyA_5, UInt<1>("h0")) @[ArbiterTree.scala 88:39]
    node _io_out_T_35 = and(_io_out_T_33, _io_out_T_34) @[ArbiterTree.scala 88:37]
    node _GEN_50 = mux(_io_out_T_35, UInt<1>("h1"), io_out_regReadyB_5) @[ArbiterTree.scala 88:51 89:17 82:28]
    node _GEN_51 = mux(_io_out_T_32, UInt<1>("h1"), io_out_regReadyA_5) @[ArbiterTree.scala 86:44 87:17 81:28]
    node _GEN_52 = mux(_io_out_T_32, io_out_regReadyB_5, _GEN_50) @[ArbiterTree.scala 82:28 86:44]
    node io_out_out_3_bits = io_out_regData_3 @[ArbiterTree.scala 110:14 84:19]
    node _GEN_53 = mux(io_out_regReadyA_5, io_out_out_3_bits, io_out_regData_5) @[ArbiterTree.scala 94:22 95:15 79:22]
    node _GEN_54 = mux(io_out_regReadyA_5, UInt<1>("h0"), io_out_regEmpty_5) @[ArbiterTree.scala 94:22 96:16 80:27]
    node _GEN_55 = mux(io_out_regReadyA_5, UInt<1>("h0"), _GEN_51) @[ArbiterTree.scala 94:22 97:17]
    node io_out_out_4_bits = io_out_regData_4 @[ArbiterTree.scala 110:14 84:19]
    node _GEN_56 = mux(io_out_regReadyB_5, io_out_out_4_bits, _GEN_53) @[ArbiterTree.scala 100:15 99:22]
    node _GEN_57 = mux(io_out_regReadyB_5, UInt<1>("h0"), _GEN_54) @[ArbiterTree.scala 101:16 99:22]
    node _GEN_58 = mux(io_out_regReadyB_5, UInt<1>("h0"), _GEN_52) @[ArbiterTree.scala 102:17 99:22]
    node _io_out_out_valid_T_5 = eq(io_out_regEmpty_5, UInt<1>("h0")) @[ArbiterTree.scala 105:18]
    node io_out_out_5_ready = io_out_ready @[ArbiterTree.scala 116:10 84:19]
    node _GEN_59 = mux(io_out_out_5_ready, UInt<1>("h1"), _GEN_57) @[ArbiterTree.scala 106:22 107:16]
    node io_out_out_5_valid = _io_out_out_valid_T_5 @[ArbiterTree.scala 105:15 84:19]
    node io_out_out_5_bits = io_out_regData_5 @[ArbiterTree.scala 110:14 84:19]
    io_in_0_ready <= io_out_regReadyA_3 @[ArbiterTree.scala 91:13]
    io_in_1_ready <= io_out_regReadyA @[ArbiterTree.scala 91:13]
    io_in_2_ready <= io_out_regReadyB @[ArbiterTree.scala 92:13]
    io_in_3_ready <= io_out_regReadyA_1 @[ArbiterTree.scala 91:13]
    io_in_4_ready <= io_out_regReadyB_1 @[ArbiterTree.scala 92:13]
    io_in_5_ready <= io_out_regReadyA_2 @[ArbiterTree.scala 91:13]
    io_in_6_ready <= io_out_regReadyB_2 @[ArbiterTree.scala 92:13]
    io_out_valid <= io_out_out_5_valid @[ArbiterTree.scala 116:10]
    io_out_bits <= io_out_out_5_bits @[ArbiterTree.scala 116:10]
    io_out_regData <= _GEN_6
    io_out_regEmpty <= mux(reset1, UInt<1>("h1"), _GEN_9) @[ArbiterTree.scala 80:{27,27}]
    io_out_regReadyA <= mux(reset1, UInt<1>("h0"), _GEN_5) @[ArbiterTree.scala 81:{28,28}]
    io_out_regReadyB <= mux(reset1, UInt<1>("h0"), _GEN_8) @[ArbiterTree.scala 82:{28,28}]
    io_out_regData_1 <= _GEN_16
    io_out_regEmpty_1 <= mux(reset1, UInt<1>("h1"), _GEN_19) @[ArbiterTree.scala 80:{27,27}]
    io_out_regReadyA_1 <= mux(reset1, UInt<1>("h0"), _GEN_15) @[ArbiterTree.scala 81:{28,28}]
    io_out_regReadyB_1 <= mux(reset1, UInt<1>("h0"), _GEN_18) @[ArbiterTree.scala 82:{28,28}]
    io_out_regData_2 <= _GEN_26
    io_out_regEmpty_2 <= mux(reset1, UInt<1>("h1"), _GEN_29) @[ArbiterTree.scala 80:{27,27}]
    io_out_regReadyA_2 <= mux(reset1, UInt<1>("h0"), _GEN_25) @[ArbiterTree.scala 81:{28,28}]
    io_out_regReadyB_2 <= mux(reset1, UInt<1>("h0"), _GEN_28) @[ArbiterTree.scala 82:{28,28}]
    io_out_regData_3 <= _GEN_36
    io_out_regEmpty_3 <= mux(reset1, UInt<1>("h1"), _GEN_39) @[ArbiterTree.scala 80:{27,27}]
    io_out_regReadyA_3 <= mux(reset1, UInt<1>("h0"), _GEN_35) @[ArbiterTree.scala 81:{28,28}]
    io_out_regReadyB_3 <= mux(reset1, UInt<1>("h0"), _GEN_38) @[ArbiterTree.scala 82:{28,28}]
    io_out_regData_4 <= _GEN_46
    io_out_regEmpty_4 <= mux(reset1, UInt<1>("h1"), _GEN_49) @[ArbiterTree.scala 80:{27,27}]
    io_out_regReadyA_4 <= mux(reset1, UInt<1>("h0"), _GEN_45) @[ArbiterTree.scala 81:{28,28}]
    io_out_regReadyB_4 <= mux(reset1, UInt<1>("h0"), _GEN_48) @[ArbiterTree.scala 82:{28,28}]
    io_out_regData_5 <= _GEN_56
    io_out_regEmpty_5 <= mux(reset1, UInt<1>("h1"), _GEN_59) @[ArbiterTree.scala 80:{27,27}]
    io_out_regReadyA_5 <= mux(reset1, UInt<1>("h0"), _GEN_55) @[ArbiterTree.scala 81:{28,28}]
    io_out_regReadyB_5 <= mux(reset1, UInt<1>("h0"), _GEN_58) @[ArbiterTree.scala 82:{28,28}]
