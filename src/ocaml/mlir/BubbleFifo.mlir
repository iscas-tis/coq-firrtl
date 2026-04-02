// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @BubbleFifo(in %clock1: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_enq_write: !firrtl.uint<1>, out %io_enq_full: !firrtl.uint<1>, in %io_enq_din: !firrtl.uint<8>, in %io_deq_read: !firrtl.uint<1>, out %io_deq_empty: !firrtl.uint<1>, out %io_deq_dout: !firrtl.uint<8>) attributes {convention = #firrtl<convention scalarized>} {
  %io_enq_write_0 = firrtl.wire {name = "io_enq_write"} : !firrtl.uint<1>
  %io_enq_full_1 = firrtl.wire {name = "io_enq_full"} : !firrtl.uint<1>
  %io_enq_din_2 = firrtl.wire {name = "io_enq_din"} : !firrtl.uint<8>
  %io_deq_read_3 = firrtl.wire {name = "io_deq_read"} : !firrtl.uint<1>
  %io_deq_empty_4 = firrtl.wire {name = "io_deq_empty"} : !firrtl.uint<1>
  %io_deq_dout_5 = firrtl.wire {name = "io_deq_dout"} : !firrtl.uint<8>
  firrtl.strictconnect %io_enq_write_0, %io_enq_write : !firrtl.uint<1>
  firrtl.strictconnect %io_enq_full, %io_enq_full_1 : !firrtl.uint<1>
  firrtl.strictconnect %io_enq_din_2, %io_enq_din : !firrtl.uint<8>
  firrtl.strictconnect %io_deq_read_3, %io_deq_read : !firrtl.uint<1>
  firrtl.strictconnect %io_deq_empty, %io_deq_empty_4 : !firrtl.uint<1>
  firrtl.strictconnect %io_deq_dout, %io_deq_dout_5 : !firrtl.uint<8>
  %FifoRegister_clock, %FifoRegister_reset, %FifoRegister_io_enq_write, %FifoRegister_io_enq_full, %FifoRegister_io_enq_din, %FifoRegister_io_deq_read, %FifoRegister_io_deq_empty, %FifoRegister_io_deq_dout = firrtl.instance FifoRegister @FifoRegister(in clock1: !firrtl.clock, in reset1: !firrtl.uint<1>, in io_enq_write: !firrtl.uint<1>, out io_enq_full: !firrtl.uint<1>, in io_enq_din: !firrtl.uint<8>, in io_deq_read: !firrtl.uint<1>, out io_deq_empty: !firrtl.uint<1>, out io_deq_dout: !firrtl.uint<8>)
  %FifoRegister.io_enq_write = firrtl.wire : !firrtl.uint<1>
  %FifoRegister.io_enq_full = firrtl.wire : !firrtl.uint<1>
  %FifoRegister.io_enq_din = firrtl.wire : !firrtl.uint<8>
  %FifoRegister.io_deq_read = firrtl.wire : !firrtl.uint<1>
  %FifoRegister.io_deq_empty = firrtl.wire : !firrtl.uint<1>
  %FifoRegister.io_deq_dout = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_io_enq_write, %FifoRegister.io_enq_write : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister.io_enq_full, %FifoRegister_io_enq_full : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_io_enq_din, %FifoRegister.io_enq_din : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_io_deq_read, %FifoRegister.io_deq_read : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister.io_deq_empty, %FifoRegister_io_deq_empty : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister.io_deq_dout, %FifoRegister_io_deq_dout : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_clock, %clock1 : !firrtl.clock
  firrtl.strictconnect %FifoRegister_reset, %reset1 : !firrtl.uint<1>
  %FifoRegister_1_clock, %FifoRegister_1_reset, %FifoRegister_1_io_enq_write, %FifoRegister_1_io_enq_full, %FifoRegister_1_io_enq_din, %FifoRegister_1_io_deq_read, %FifoRegister_1_io_deq_empty, %FifoRegister_1_io_deq_dout = firrtl.instance FifoRegister_1 @FifoRegister(in clock1: !firrtl.clock, in reset1: !firrtl.uint<1>, in io_enq_write: !firrtl.uint<1>, out io_enq_full: !firrtl.uint<1>, in io_enq_din: !firrtl.uint<8>, in io_deq_read: !firrtl.uint<1>, out io_deq_empty: !firrtl.uint<1>, out io_deq_dout: !firrtl.uint<8>)
  %FifoRegister_1.io_enq_write = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_1.io_enq_full = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_1.io_enq_din = firrtl.wire : !firrtl.uint<8>
  %FifoRegister_1.io_deq_read = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_1.io_deq_empty = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_1.io_deq_dout = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_1_io_enq_write, %FifoRegister_1.io_enq_write : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_1.io_enq_full, %FifoRegister_1_io_enq_full : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_1_io_enq_din, %FifoRegister_1.io_enq_din : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_1_io_deq_read, %FifoRegister_1.io_deq_read : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_1.io_deq_empty, %FifoRegister_1_io_deq_empty : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_1.io_deq_dout, %FifoRegister_1_io_deq_dout : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_1_clock, %clock1 : !firrtl.clock
  firrtl.strictconnect %FifoRegister_1_reset, %reset1 : !firrtl.uint<1>
  %FifoRegister_2_clock, %FifoRegister_2_reset, %FifoRegister_2_io_enq_write, %FifoRegister_2_io_enq_full, %FifoRegister_2_io_enq_din, %FifoRegister_2_io_deq_read, %FifoRegister_2_io_deq_empty, %FifoRegister_2_io_deq_dout = firrtl.instance FifoRegister_2 @FifoRegister(in clock1: !firrtl.clock, in reset1: !firrtl.uint<1>, in io_enq_write: !firrtl.uint<1>, out io_enq_full: !firrtl.uint<1>, in io_enq_din: !firrtl.uint<8>, in io_deq_read: !firrtl.uint<1>, out io_deq_empty: !firrtl.uint<1>, out io_deq_dout: !firrtl.uint<8>)
  %FifoRegister_2.io_enq_write = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_2.io_enq_full = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_2.io_enq_din = firrtl.wire : !firrtl.uint<8>
  %FifoRegister_2.io_deq_read = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_2.io_deq_empty = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_2.io_deq_dout = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_2_io_enq_write, %FifoRegister_2.io_enq_write : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_2.io_enq_full, %FifoRegister_2_io_enq_full : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_2_io_enq_din, %FifoRegister_2.io_enq_din : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_2_io_deq_read, %FifoRegister_2.io_deq_read : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_2.io_deq_empty, %FifoRegister_2_io_deq_empty : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_2.io_deq_dout, %FifoRegister_2_io_deq_dout : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_2_clock, %clock1 : !firrtl.clock
  firrtl.strictconnect %FifoRegister_2_reset, %reset1 : !firrtl.uint<1>
  %FifoRegister_3_clock, %FifoRegister_3_reset, %FifoRegister_3_io_enq_write, %FifoRegister_3_io_enq_full, %FifoRegister_3_io_enq_din, %FifoRegister_3_io_deq_read, %FifoRegister_3_io_deq_empty, %FifoRegister_3_io_deq_dout = firrtl.instance FifoRegister_3 @FifoRegister(in clock1: !firrtl.clock, in reset1: !firrtl.uint<1>, in io_enq_write: !firrtl.uint<1>, out io_enq_full: !firrtl.uint<1>, in io_enq_din: !firrtl.uint<8>, in io_deq_read: !firrtl.uint<1>, out io_deq_empty: !firrtl.uint<1>, out io_deq_dout: !firrtl.uint<8>)
  %FifoRegister_3.io_enq_write = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_3.io_enq_full = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_3.io_enq_din = firrtl.wire : !firrtl.uint<8>
  %FifoRegister_3.io_deq_read = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_3.io_deq_empty = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_3.io_deq_dout = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_3_io_enq_write, %FifoRegister_3.io_enq_write : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_3.io_enq_full, %FifoRegister_3_io_enq_full : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_3_io_enq_din, %FifoRegister_3.io_enq_din : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_3_io_deq_read, %FifoRegister_3.io_deq_read : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_3.io_deq_empty, %FifoRegister_3_io_deq_empty : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_3.io_deq_dout, %FifoRegister_3_io_deq_dout : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_3_clock, %clock1 : !firrtl.clock
  firrtl.strictconnect %FifoRegister_3_reset, %reset1 : !firrtl.uint<1>
  %FifoRegister_4_clock, %FifoRegister_4_reset, %FifoRegister_4_io_enq_write, %FifoRegister_4_io_enq_full, %FifoRegister_4_io_enq_din, %FifoRegister_4_io_deq_read, %FifoRegister_4_io_deq_empty, %FifoRegister_4_io_deq_dout = firrtl.instance FifoRegister_4 @FifoRegister(in clock1: !firrtl.clock, in reset1: !firrtl.uint<1>, in io_enq_write: !firrtl.uint<1>, out io_enq_full: !firrtl.uint<1>, in io_enq_din: !firrtl.uint<8>, in io_deq_read: !firrtl.uint<1>, out io_deq_empty: !firrtl.uint<1>, out io_deq_dout: !firrtl.uint<8>)
  %FifoRegister_4.io_enq_write = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_4.io_enq_full = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_4.io_enq_din = firrtl.wire : !firrtl.uint<8>
  %FifoRegister_4.io_deq_read = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_4.io_deq_empty = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_4.io_deq_dout = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_4_io_enq_write, %FifoRegister_4.io_enq_write : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_4.io_enq_full, %FifoRegister_4_io_enq_full : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_4_io_enq_din, %FifoRegister_4.io_enq_din : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_4_io_deq_read, %FifoRegister_4.io_deq_read : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_4.io_deq_empty, %FifoRegister_4_io_deq_empty : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_4.io_deq_dout, %FifoRegister_4_io_deq_dout : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_4_clock, %clock1 : !firrtl.clock
  firrtl.strictconnect %FifoRegister_4_reset, %reset1 : !firrtl.uint<1>
  %FifoRegister_5_clock, %FifoRegister_5_reset, %FifoRegister_5_io_enq_write, %FifoRegister_5_io_enq_full, %FifoRegister_5_io_enq_din, %FifoRegister_5_io_deq_read, %FifoRegister_5_io_deq_empty, %FifoRegister_5_io_deq_dout = firrtl.instance FifoRegister_5 @FifoRegister(in clock1: !firrtl.clock, in reset1: !firrtl.uint<1>, in io_enq_write: !firrtl.uint<1>, out io_enq_full: !firrtl.uint<1>, in io_enq_din: !firrtl.uint<8>, in io_deq_read: !firrtl.uint<1>, out io_deq_empty: !firrtl.uint<1>, out io_deq_dout: !firrtl.uint<8>)
  %FifoRegister_5.io_enq_write = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_5.io_enq_full = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_5.io_enq_din = firrtl.wire : !firrtl.uint<8>
  %FifoRegister_5.io_deq_read = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_5.io_deq_empty = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_5.io_deq_dout = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_5_io_enq_write, %FifoRegister_5.io_enq_write : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_5.io_enq_full, %FifoRegister_5_io_enq_full : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_5_io_enq_din, %FifoRegister_5.io_enq_din : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_5_io_deq_read, %FifoRegister_5.io_deq_read : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_5.io_deq_empty, %FifoRegister_5_io_deq_empty : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_5.io_deq_dout, %FifoRegister_5_io_deq_dout : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_5_clock, %clock1 : !firrtl.clock
  firrtl.strictconnect %FifoRegister_5_reset, %reset1 : !firrtl.uint<1>
  %FifoRegister_6_clock, %FifoRegister_6_reset, %FifoRegister_6_io_enq_write, %FifoRegister_6_io_enq_full, %FifoRegister_6_io_enq_din, %FifoRegister_6_io_deq_read, %FifoRegister_6_io_deq_empty, %FifoRegister_6_io_deq_dout = firrtl.instance FifoRegister_6 @FifoRegister(in clock1: !firrtl.clock, in reset1: !firrtl.uint<1>, in io_enq_write: !firrtl.uint<1>, out io_enq_full: !firrtl.uint<1>, in io_enq_din: !firrtl.uint<8>, in io_deq_read: !firrtl.uint<1>, out io_deq_empty: !firrtl.uint<1>, out io_deq_dout: !firrtl.uint<8>)
  %FifoRegister_6.io_enq_write = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_6.io_enq_full = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_6.io_enq_din = firrtl.wire : !firrtl.uint<8>
  %FifoRegister_6.io_deq_read = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_6.io_deq_empty = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_6.io_deq_dout = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_6_io_enq_write, %FifoRegister_6.io_enq_write : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_6.io_enq_full, %FifoRegister_6_io_enq_full : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_6_io_enq_din, %FifoRegister_6.io_enq_din : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_6_io_deq_read, %FifoRegister_6.io_deq_read : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_6.io_deq_empty, %FifoRegister_6_io_deq_empty : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_6.io_deq_dout, %FifoRegister_6_io_deq_dout : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_6_clock, %clock1 : !firrtl.clock
  firrtl.strictconnect %FifoRegister_6_reset, %reset1 : !firrtl.uint<1>
  %FifoRegister_7_clock, %FifoRegister_7_reset, %FifoRegister_7_io_enq_write, %FifoRegister_7_io_enq_full, %FifoRegister_7_io_enq_din, %FifoRegister_7_io_deq_read, %FifoRegister_7_io_deq_empty, %FifoRegister_7_io_deq_dout = firrtl.instance FifoRegister_7 @FifoRegister(in clock1: !firrtl.clock, in reset1: !firrtl.uint<1>, in io_enq_write: !firrtl.uint<1>, out io_enq_full: !firrtl.uint<1>, in io_enq_din: !firrtl.uint<8>, in io_deq_read: !firrtl.uint<1>, out io_deq_empty: !firrtl.uint<1>, out io_deq_dout: !firrtl.uint<8>)
  %FifoRegister_7.io_enq_write = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_7.io_enq_full = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_7.io_enq_din = firrtl.wire : !firrtl.uint<8>
  %FifoRegister_7.io_deq_read = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_7.io_deq_empty = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_7.io_deq_dout = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_7_io_enq_write, %FifoRegister_7.io_enq_write : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_7.io_enq_full, %FifoRegister_7_io_enq_full : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_7_io_enq_din, %FifoRegister_7.io_enq_din : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_7_io_deq_read, %FifoRegister_7.io_deq_read : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_7.io_deq_empty, %FifoRegister_7_io_deq_empty : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_7.io_deq_dout, %FifoRegister_7_io_deq_dout : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_7_clock, %clock1 : !firrtl.clock
  firrtl.strictconnect %FifoRegister_7_reset, %reset1 : !firrtl.uint<1>
  %FifoRegister_8_clock, %FifoRegister_8_reset, %FifoRegister_8_io_enq_write, %FifoRegister_8_io_enq_full, %FifoRegister_8_io_enq_din, %FifoRegister_8_io_deq_read, %FifoRegister_8_io_deq_empty, %FifoRegister_8_io_deq_dout = firrtl.instance FifoRegister_8 @FifoRegister(in clock1: !firrtl.clock, in reset1: !firrtl.uint<1>, in io_enq_write: !firrtl.uint<1>, out io_enq_full: !firrtl.uint<1>, in io_enq_din: !firrtl.uint<8>, in io_deq_read: !firrtl.uint<1>, out io_deq_empty: !firrtl.uint<1>, out io_deq_dout: !firrtl.uint<8>)
  %FifoRegister_8.io_enq_write = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_8.io_enq_full = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_8.io_enq_din = firrtl.wire : !firrtl.uint<8>
  %FifoRegister_8.io_deq_read = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_8.io_deq_empty = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_8.io_deq_dout = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_8_io_enq_write, %FifoRegister_8.io_enq_write : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_8.io_enq_full, %FifoRegister_8_io_enq_full : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_8_io_enq_din, %FifoRegister_8.io_enq_din : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_8_io_deq_read, %FifoRegister_8.io_deq_read : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_8.io_deq_empty, %FifoRegister_8_io_deq_empty : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_8.io_deq_dout, %FifoRegister_8_io_deq_dout : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_8_clock, %clock1 : !firrtl.clock
  firrtl.strictconnect %FifoRegister_8_reset, %reset1 : !firrtl.uint<1>
  %FifoRegister_9_clock, %FifoRegister_9_reset, %FifoRegister_9_io_enq_write, %FifoRegister_9_io_enq_full, %FifoRegister_9_io_enq_din, %FifoRegister_9_io_deq_read, %FifoRegister_9_io_deq_empty, %FifoRegister_9_io_deq_dout = firrtl.instance FifoRegister_9 @FifoRegister(in clock1: !firrtl.clock, in reset1: !firrtl.uint<1>, in io_enq_write: !firrtl.uint<1>, out io_enq_full: !firrtl.uint<1>, in io_enq_din: !firrtl.uint<8>, in io_deq_read: !firrtl.uint<1>, out io_deq_empty: !firrtl.uint<1>, out io_deq_dout: !firrtl.uint<8>)
  %FifoRegister_9.io_enq_write = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_9.io_enq_full = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_9.io_enq_din = firrtl.wire : !firrtl.uint<8>
  %FifoRegister_9.io_deq_read = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_9.io_deq_empty = firrtl.wire : !firrtl.uint<1>
  %FifoRegister_9.io_deq_dout = firrtl.wire : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_9_io_enq_write, %FifoRegister_9.io_enq_write : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_9.io_enq_full, %FifoRegister_9_io_enq_full : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_9_io_enq_din, %FifoRegister_9.io_enq_din : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_9_io_deq_read, %FifoRegister_9.io_deq_read : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_9.io_deq_empty, %FifoRegister_9_io_deq_empty : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_9.io_deq_dout, %FifoRegister_9_io_deq_dout : !firrtl.uint<8>
  firrtl.strictconnect %FifoRegister_9_clock, %clock1 : !firrtl.clock
  firrtl.strictconnect %FifoRegister_9_reset, %reset1 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_1.io_enq_din, %FifoRegister.io_deq_dout : !firrtl.uint<8>
  %0 = firrtl.not %FifoRegister.io_deq_empty : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %1 = firrtl.node %0 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_1.io_enq_write, %1 : !firrtl.uint<1>
  %2 = firrtl.not %FifoRegister_1.io_enq_full : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %3 = firrtl.node %2 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister.io_deq_read, %3 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_2.io_enq_din, %FifoRegister_1.io_deq_dout : !firrtl.uint<8>
  %4 = firrtl.not %FifoRegister_1.io_deq_empty : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %5 = firrtl.node %4 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_2.io_enq_write, %5 : !firrtl.uint<1>
  %6 = firrtl.not %FifoRegister_2.io_enq_full : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %7 = firrtl.node %6 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_1.io_deq_read, %7 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_3.io_enq_din, %FifoRegister_2.io_deq_dout : !firrtl.uint<8>
  %8 = firrtl.not %FifoRegister_2.io_deq_empty : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %9 = firrtl.node %8 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_3.io_enq_write, %9 : !firrtl.uint<1>
  %10 = firrtl.not %FifoRegister_3.io_enq_full : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %11 = firrtl.node %10 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_2.io_deq_read, %11 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_4.io_enq_din, %FifoRegister_3.io_deq_dout : !firrtl.uint<8>
  %12 = firrtl.not %FifoRegister_3.io_deq_empty : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %13 = firrtl.node %12 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_4.io_enq_write, %13 : !firrtl.uint<1>
  %14 = firrtl.not %FifoRegister_4.io_enq_full : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %15 = firrtl.node %14 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_3.io_deq_read, %15 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_5.io_enq_din, %FifoRegister_4.io_deq_dout : !firrtl.uint<8>
  %16 = firrtl.not %FifoRegister_4.io_deq_empty : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %17 = firrtl.node %16 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_5.io_enq_write, %17 : !firrtl.uint<1>
  %18 = firrtl.not %FifoRegister_5.io_enq_full : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %19 = firrtl.node %18 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_4.io_deq_read, %19 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_6.io_enq_din, %FifoRegister_5.io_deq_dout : !firrtl.uint<8>
  %20 = firrtl.not %FifoRegister_5.io_deq_empty : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %21 = firrtl.node %20 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_6.io_enq_write, %21 : !firrtl.uint<1>
  %22 = firrtl.not %FifoRegister_6.io_enq_full : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %23 = firrtl.node %22 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_5.io_deq_read, %23 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_7.io_enq_din, %FifoRegister_6.io_deq_dout : !firrtl.uint<8>
  %24 = firrtl.not %FifoRegister_6.io_deq_empty : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %25 = firrtl.node %24 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_7.io_enq_write, %25 : !firrtl.uint<1>
  %26 = firrtl.not %FifoRegister_7.io_enq_full : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %27 = firrtl.node %26 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_6.io_deq_read, %27 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_8.io_enq_din, %FifoRegister_7.io_deq_dout : !firrtl.uint<8>
  %28 = firrtl.not %FifoRegister_7.io_deq_empty : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %29 = firrtl.node %28 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_8.io_enq_write, %29 : !firrtl.uint<1>
  %30 = firrtl.not %FifoRegister_8.io_enq_full : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %31 = firrtl.node %30 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_7.io_deq_read, %31 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_9.io_enq_din, %FifoRegister_8.io_deq_dout : !firrtl.uint<8>
  %32 = firrtl.not %FifoRegister_8.io_deq_empty : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %33 = firrtl.node %32 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_9.io_enq_write, %33 : !firrtl.uint<1>
  %34 = firrtl.not %FifoRegister_9.io_enq_full : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %35 = firrtl.node %34 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_8.io_deq_read, %35 : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister.io_enq_din, %io_enq_din_2 : !firrtl.uint<8>
  firrtl.strictconnect %io_enq_full_1, %FifoRegister.io_enq_full : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister.io_enq_write, %io_enq_write_0 : !firrtl.uint<1>
  firrtl.strictconnect %io_deq_dout_5, %FifoRegister_9.io_deq_dout : !firrtl.uint<8>
  firrtl.strictconnect %io_deq_empty_4, %FifoRegister_9.io_deq_empty : !firrtl.uint<1>
  firrtl.strictconnect %FifoRegister_9.io_deq_read, %io_deq_read_3 : !firrtl.uint<1>
}

// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module private @FifoRegister(in %clock1: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_enq_write: !firrtl.uint<1>, out %io_enq_full: !firrtl.uint<1>, in %io_enq_din: !firrtl.uint<8>, in %io_deq_read: !firrtl.uint<1>, out %io_deq_empty: !firrtl.uint<1>, out %io_deq_dout: !firrtl.uint<8>) {
  %io_enq_write_0 = firrtl.wire {name = "io_enq_write"} : !firrtl.uint<1>
  %io_enq_full_1 = firrtl.wire {name = "io_enq_full"} : !firrtl.uint<1>
  %io_enq_din_2 = firrtl.wire {name = "io_enq_din"} : !firrtl.uint<8>
  %io_deq_read_3 = firrtl.wire {name = "io_deq_read"} : !firrtl.uint<1>
  %io_deq_empty_4 = firrtl.wire {name = "io_deq_empty"} : !firrtl.uint<1>
  %io_deq_dout_5 = firrtl.wire {name = "io_deq_dout"} : !firrtl.uint<8>
  firrtl.strictconnect %io_enq_write_0, %io_enq_write : !firrtl.uint<1>
  firrtl.strictconnect %io_enq_full, %io_enq_full_1 : !firrtl.uint<1>
  firrtl.strictconnect %io_enq_din_2, %io_enq_din : !firrtl.uint<8>
  firrtl.strictconnect %io_deq_read_3, %io_deq_read : !firrtl.uint<1>
  firrtl.strictconnect %io_deq_empty, %io_deq_empty_4 : !firrtl.uint<1>
  firrtl.strictconnect %io_deq_dout, %io_deq_dout_5 : !firrtl.uint<8>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %stateReg = firrtl.regreset %clock1, %reset1, %c0_ui1 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>
  %c0_ui8 = firrtl.constant 0 : !firrtl.uint<8>
  %dataReg = firrtl.regreset %clock1, %reset1, %c0_ui8 : !firrtl.clock, !firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>
  %0 = firrtl.eq %stateReg, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %1 = firrtl.node %0 : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %2 = firrtl.and %1, %io_enq_write_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %3 = firrtl.mux(%io_enq_write_0, %c1_ui1, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %4 = firrtl.mux(%io_enq_write_0, %io_enq_din_2, %dataReg) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %5 = firrtl.not %1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %6 = firrtl.eq %stateReg, %c1_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %7 = firrtl.node %6 : !firrtl.uint<1>
  %8 = firrtl.and %5, %7 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %9 = firrtl.and %8, %io_deq_read_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %10 = firrtl.mux(%io_deq_read_3, %c0_ui1, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %11 = firrtl.mux(%7, %10, %stateReg) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %12 = firrtl.mux(%1, %3, %11) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.connect %stateReg, %12 : !firrtl.uint<1>, !firrtl.uint<1>
  %13 = firrtl.pad %c0_ui1, 8 : (!firrtl.uint<1>) -> !firrtl.uint<8>
  %14 = firrtl.mux(%io_deq_read_3, %13, %dataReg) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %15 = firrtl.mux(%7, %14, %dataReg) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  %16 = firrtl.mux(%1, %4, %15) : (!firrtl.uint<1>, !firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
  firrtl.connect %dataReg, %16 : !firrtl.uint<8>, !firrtl.uint<8>
  %17 = firrtl.not %7 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %18 = firrtl.and %5, %17 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %19 = firrtl.eq %stateReg, %c1_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %_io_enq_full_T = firrtl.node %19 : !firrtl.uint<1>
  firrtl.strictconnect %io_enq_full_1, %_io_enq_full_T : !firrtl.uint<1>
  %_io_deq_empty_T = firrtl.node %0 : !firrtl.uint<1>
  firrtl.strictconnect %io_deq_empty_4, %_io_deq_empty_T : !firrtl.uint<1>
  firrtl.strictconnect %io_deq_dout_5, %dataReg : !firrtl.uint<8>
}

