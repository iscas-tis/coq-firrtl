circuit fib :
  module fib :
    input go : UInt < 1 > 
    input reset1 : UInt < 1 > 
    input clk : Clock
    output out : UInt < 4 > 

    reg n : UInt < 4 > , clk with :
      reset => ( UInt < 1 > ( "h0" ) , n ) 
    reg m : UInt < 4 > , clk with :
      reset => ( UInt < 1 > ( "h0" ) , m ) 
    out <= n
    n <= mux ( reset1 , UInt < 4 > ( "h0" ) , mux ( go , m , n ) ) 
    m <= mux ( reset1 , UInt < 4 > ( "h1" ) , bits ( mux ( go , add ( n , m ) , m ) , 3 , 0 ) ) 
    