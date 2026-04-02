// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @Comparator(in %clock: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_a: !firrtl.uint<8>, in %io_b: !firrtl.uint<8>, out %io_equ: !firrtl.uint<1>, out %io_gt1: !firrtl.uint<1>) attributes {convention = #firrtl<convention scalarized>} {
  %io_a_0 = firrtl.wire {name = "io_a"} : !firrtl.uint<8>
  %io_b_1 = firrtl.wire {name = "io_b"} : !firrtl.uint<8>
  %io_equ_2 = firrtl.wire {name = "io_equ"} : !firrtl.uint<1>
  %io_gt1_3 = firrtl.wire {name = "io_gt1"} : !firrtl.uint<1>
  firrtl.strictconnect %io_a_0, %io_a : !firrtl.uint<8>
  firrtl.strictconnect %io_b_1, %io_b : !firrtl.uint<8>
  firrtl.strictconnect %io_equ, %io_equ_2 : !firrtl.uint<1>
  firrtl.strictconnect %io_gt1, %io_gt1_3 : !firrtl.uint<1>
  %0 = firrtl.eq %io_a_0, %io_b_1 : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<1>
  %equ = firrtl.node %0 : !firrtl.uint<1>
  %1 = firrtl.gt %io_a_0, %io_b_1 : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<1>
  %gt1 = firrtl.node %1 : !firrtl.uint<1>
  firrtl.strictconnect %io_equ_2, %equ : !firrtl.uint<1>
  firrtl.strictconnect %io_gt1_3, %gt1 : !firrtl.uint<1>
}

