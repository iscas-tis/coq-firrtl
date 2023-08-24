circuit Arbiter3Loop :
  module Arbiter3Loop :
    input clock : Clock
    input reset1 : UInt<1>
    input io_request : UInt<3>
    output io_grant : UInt<3>

    node _request_T = bits(io_request, 0, 0) @[arbiter.scala 73:36]
    node _request_T_1 = bits(io_request, 1, 1) @[arbiter.scala 73:36]
    node _request_T_2 = bits(io_request, 2, 2) @[arbiter.scala 73:36]
    node request_0 = _request_T @[arbiter.scala 73:{24,24}]
    node grant_0 = request_0 @[arbiter.scala 77:30 80:12]
    node _notGranted_0_T = eq(grant_0, UInt<1>("h0")) @[arbiter.scala 81:20]
    node request_1 = _request_T_1 @[arbiter.scala 73:{24,24}]
    node notGranted_0 = _notGranted_0_T @[arbiter.scala 78:35 81:17]
    node _grant_1_T = and(request_1, notGranted_0) @[arbiter.scala 83:28]
    node grant_1 = _grant_1_T @[arbiter.scala 77:30 83:14]
    node _notGranted_1_T = eq(grant_1, UInt<1>("h0")) @[arbiter.scala 84:22]
    node _notGranted_1_T_1 = and(_notGranted_1_T, notGranted_0) @[arbiter.scala 84:32]
    node request_2 = _request_T_2 @[arbiter.scala 73:{24,24}]
    node notGranted_1 = _notGranted_1_T_1 @[arbiter.scala 78:35 84:19]
    node _grant_2_T = and(request_2, notGranted_1) @[arbiter.scala 83:28]
    node grant_2 = _grant_2_T @[arbiter.scala 77:30 83:14]
    node _notGranted_2_T = eq(grant_2, UInt<1>("h0")) @[arbiter.scala 84:22]
    node _notGranted_2_T_1 = and(_notGranted_2_T, notGranted_1) @[arbiter.scala 84:32]
    node io_grant_hi = cat(grant_2, grant_1) @[arbiter.scala 88:21]
    node _io_grant_T = cat(io_grant_hi, grant_0) @[arbiter.scala 88:21]
    node notGranted_2 = _notGranted_2_T_1 @[arbiter.scala 78:35 84:19]
    io_grant <= _io_grant_T @[arbiter.scala 88:12]
