circuit BasicExercise :
  module BasicExercise :
    input clock : Clock
    input reset1 : UInt<1>
    input io_sw : UInt<2>
    output io_led : UInt<1>

    node _io_led_T = bits(io_sw, 0, 0) @[Snippets.scala 20:18]
    node _io_led_T_1 = bits(io_sw, 1, 1) @[Snippets.scala 20:29]
    node _io_led_T_2 = and(_io_led_T, _io_led_T_1) @[Snippets.scala 20:22]
    io_led <= _io_led_T_2 @[Snippets.scala 20:10]
