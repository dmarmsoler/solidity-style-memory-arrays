// ./docker_solcmc examples test03.sol test03 60 eld -horn
// ./docker_solcmc examples test03.sol test03 60 z3

contract test03 {
   
    constructor() {
    }

    function t03(uint8[20] memory x, uint8 i, uint8 y) 
    pure
    public 
    returns (uint8[20] memory)  
    {
      x[i] = y;
      assert (x[i]==y);
      return x;
    }
}
