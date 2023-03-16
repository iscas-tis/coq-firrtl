circuit BundleVec :
  module BundleVec :
    input io_din : UInt<8>
    output io_dout : UInt<8>
    input io_rdIdx : UInt<2>
    input io_wrIdx : UInt<2>

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
    
    node _regVec_io_rdIdx = _GEN_8 @[BundleVec.scala 76:11]
    io_dout <= _regVec_io_rdIdx @[BundleVec.scala 76:11]
    
    regVec_0 <= _GEN_3
    regVec_1 <= _GEN_4
    regVec_2 <= _GEN_5
  