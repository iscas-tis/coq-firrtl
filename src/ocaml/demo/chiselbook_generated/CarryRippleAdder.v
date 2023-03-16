module CarryRippleAdder(
  input         clock,
  input         reset,
  input  [31:0] io_a,
  input  [31:0] io_b,
  input         io_cin,
  output [31:0] io_c,
  output        io_cout
);
  wire [32:0] _res_T = io_a + io_b; // @[Adders.scala 26:18]
  wire [32:0] _GEN_0 = {{32'd0}, io_cin}; // @[Adders.scala 26:26]
  wire [32:0] res = _res_T + _GEN_0; // @[Adders.scala 26:26]
  assign io_c = res[31:0]; // @[Adders.scala 27:17]
  assign io_cout = res[32]; // @[Adders.scala 28:17]
endmodule
