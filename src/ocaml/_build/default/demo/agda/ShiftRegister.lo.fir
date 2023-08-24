circuit ShiftRegister : @[:@2.0]
  module ShiftRegister : @[:@2.0]
    input clock : Clock @[:@4.4]
    input reset1 : UInt < 1 > @[:@5.4]
    input io_in : UInt < 1 > @[:@6.4]
    output io_out : UInt < 1 > @[:@6.4]

    reg r0 : UInt < 1 > , clock with :
      reset => ( UInt < 1 > ( "h0" ) , r0 ) @[ShiftRegister.scala 11:19:@8.4]
    reg r1 : UInt < 1 > , clock with :
      reset => ( UInt < 1 > ( "h0" ) , r1 ) @[ShiftRegister.scala 12:19:@10.4]
    reg r2 : UInt < 1 > , clock with :
      reset => ( UInt < 1 > ( "h0" ) , r2 ) @[ShiftRegister.scala 13:19:@12.4]
    reg r3 : UInt < 1 > , clock with :
      reset => ( UInt < 1 > ( "h0" ) , r3 ) @[ShiftRegister.scala 14:19:@14.4]
    io_out <= r3 @[ShiftRegister.scala 15:10:@16.4]
    r0 <= io_in @[ShiftRegister.scala 11:19:@9.4]
    r1 <= r0 @[ShiftRegister.scala 12:19:@11.4]
    r2 <= r1 @[ShiftRegister.scala 13:19:@13.4]
    r3 <= r2 @[ShiftRegister.scala 14:19:@15.4]
    skip
