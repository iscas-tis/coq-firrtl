// -----// IR Dump After ExpandWhens (firrtl-expand-whens) //----- //
firrtl.module @Arbiter3Direct(in %clock1: !firrtl.clock, in %reset1: !firrtl.uint<1>, in %io_request: !firrtl.uint<3>, out %io_grant: !firrtl.uint<3>) attributes {convention = #firrtl<convention scalarized>} {
  %io_request_0 = firrtl.wire {name = "io_request"} : !firrtl.uint<3>
  %io_grant_1 = firrtl.wire {name = "io_grant"} : !firrtl.uint<3>
  firrtl.strictconnect %io_request_0, %io_request : !firrtl.uint<3>
  firrtl.strictconnect %io_grant, %io_grant_1 : !firrtl.uint<3>
  %grant = firrtl.wire : !firrtl.uint<3>
  %c0_ui3 = firrtl.constant 0 : !firrtl.uint<3>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %0 = firrtl.eq %c0_ui1, %io_request_0 : (!firrtl.uint<1>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %1 = firrtl.node %0 : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %c2_ui2 = firrtl.constant 2 : !firrtl.uint<2>
  %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
  %c4_ui3 = firrtl.constant 4 : !firrtl.uint<3>
  %c5_ui3 = firrtl.constant 5 : !firrtl.uint<3>
  %c6_ui3 = firrtl.constant 6 : !firrtl.uint<3>
  %c7_ui3 = firrtl.constant 7 : !firrtl.uint<3>
  %2 = firrtl.pad %c0_ui1, 3 : (!firrtl.uint<1>) -> !firrtl.uint<3>
  %3 = firrtl.not %1 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %4 = firrtl.eq %c1_ui1, %io_request_0 : (!firrtl.uint<1>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %5 = firrtl.node %4 : !firrtl.uint<1>
  %6 = firrtl.and %3, %5 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %7 = firrtl.pad %c1_ui1, 3 : (!firrtl.uint<1>) -> !firrtl.uint<3>
  %8 = firrtl.not %5 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %9 = firrtl.and %3, %8 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %10 = firrtl.eq %c2_ui2, %io_request_0 : (!firrtl.uint<2>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %11 = firrtl.node %10 : !firrtl.uint<1>
  %12 = firrtl.and %9, %11 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %13 = firrtl.pad %c2_ui2, 3 : (!firrtl.uint<2>) -> !firrtl.uint<3>
  %14 = firrtl.not %11 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %15 = firrtl.and %9, %14 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %16 = firrtl.eq %c3_ui2, %io_request_0 : (!firrtl.uint<2>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %17 = firrtl.node %16 : !firrtl.uint<1>
  %18 = firrtl.and %15, %17 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %19 = firrtl.pad %c1_ui1, 3 : (!firrtl.uint<1>) -> !firrtl.uint<3>
  %20 = firrtl.not %17 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %21 = firrtl.and %15, %20 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %22 = firrtl.eq %c4_ui3, %io_request_0 : (!firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %23 = firrtl.node %22 : !firrtl.uint<1>
  %24 = firrtl.and %21, %23 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %25 = firrtl.not %23 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %26 = firrtl.and %21, %25 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %27 = firrtl.eq %c5_ui3, %io_request_0 : (!firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %28 = firrtl.node %27 : !firrtl.uint<1>
  %29 = firrtl.and %26, %28 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %30 = firrtl.pad %c1_ui1, 3 : (!firrtl.uint<1>) -> !firrtl.uint<3>
  %31 = firrtl.not %28 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %32 = firrtl.and %26, %31 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %33 = firrtl.eq %c6_ui3, %io_request_0 : (!firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %34 = firrtl.node %33 : !firrtl.uint<1>
  %35 = firrtl.and %32, %34 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %36 = firrtl.pad %c2_ui2, 3 : (!firrtl.uint<2>) -> !firrtl.uint<3>
  %37 = firrtl.not %34 : (!firrtl.uint<1>) -> !firrtl.uint<1>
  %38 = firrtl.and %32, %37 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %39 = firrtl.eq %c7_ui3, %io_request_0 : (!firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<1>
  %40 = firrtl.node %39 : !firrtl.uint<1>
  %41 = firrtl.and %38, %40 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  %42 = firrtl.pad %c1_ui1, 3 : (!firrtl.uint<1>) -> !firrtl.uint<3>
  %43 = firrtl.mux(%40, %42, %c0_ui3) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %44 = firrtl.mux(%34, %36, %43) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %45 = firrtl.mux(%28, %30, %44) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %46 = firrtl.mux(%23, %c4_ui3, %45) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %47 = firrtl.mux(%17, %19, %46) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %48 = firrtl.mux(%11, %13, %47) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %49 = firrtl.mux(%5, %7, %48) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  %50 = firrtl.mux(%1, %2, %49) : (!firrtl.uint<1>, !firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<3>
  firrtl.connect %grant, %50 : !firrtl.uint<3>, !firrtl.uint<3>
  firrtl.strictconnect %io_grant_1, %grant : !firrtl.uint<3>
}

