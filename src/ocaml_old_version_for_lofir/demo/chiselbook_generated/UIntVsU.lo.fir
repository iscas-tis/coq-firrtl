circuit UIntVsU :
  module UIntVsU :
    input clock : Clock
    input reset1 : UInt<1>
    output io_values_0 : UInt<3>
    output io_values_1 : UInt<3>
    output io_values_2 : UInt<3>
    output io_values_3 : UInt<3>
    output io_values_4 : UInt<3>

    node signed = asSInt(UInt<3>("h7")) @[UIntVsU.scala 15:{27,27}]
    node _io_values_4_T = asUInt(signed) @[UIntVsU.scala 16:18]
    io_values_0 <= UInt<3>("h7") @[UIntVsU.scala 10:8]
    io_values_1 <= UInt<3>("h7") @[UIntVsU.scala 11:8]
    io_values_2 <= UInt<3>("h7") @[UIntVsU.scala 13:8]
    io_values_3 <= UInt<3>("h7") @[UIntVsU.scala 14:8]
    io_values_4 <= _io_values_4_T @[UIntVsU.scala 16:8]
