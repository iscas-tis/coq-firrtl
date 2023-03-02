circuit FlasherBase :
  module FlasherBase :
    input clock : Clock
    input reset : UInt<1>
    output io : { flip start : UInt<1>, light : UInt<1>}

    skip

