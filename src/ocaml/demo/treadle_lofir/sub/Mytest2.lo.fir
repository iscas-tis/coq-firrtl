circuit A:
  module C:
    input cin1 : UInt<1>
    input cin2 : UInt<1>
    output cout1 : UInt<1> 
    output cout2 : UInt<1> 

    cout1 <= cin1
    cout2 <= or(cin1, cin2)

  module B:
    input bin1 : UInt<1>
    input bin2 : UInt<1>
    output bout1 : UInt<1> 
    output bout2 : UInt<1> 

    bout1 <= bin1
    bout2 <= bin2
    
  module A:
    input ain : UInt<1>
    output aout : UInt<1> 

    inst instb aof B
    inst instc aof C
    
    instc.cin1 <= instb.bout1
    instb.bin2 <= instc.cout1
    instb.bin1 <= ain
    instc.cin2 <= instb.bout2
    aout <= instc.cout2
