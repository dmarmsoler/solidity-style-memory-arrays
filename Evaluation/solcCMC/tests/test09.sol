
    // ./docker_solcmc examples test09.sol test09 60 eld -horn
    // ./docker_solcmc examples test09.sol test09 60 z3

contract test09 {
   
    constructor() {
    }

 function t09(uint8[] memory x, uint8 i, uint8 y) 
    pure 
    public 
    returns (uint8[] memory)  
    {
      x[i] = y;
      assert (x[i] == y);
      return x;
    }
}
