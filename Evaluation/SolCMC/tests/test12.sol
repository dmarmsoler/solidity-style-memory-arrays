// ./docker_solcmc examples test12.sol test12 60 eld -horn
// ./docker_solcmc examples test12.sol test12 60 z3

contract test12 {
   
    constructor() {
    }

  function t12(uint8[20][20] memory x, uint8 i, uint8 j, uint8 k, uint8 value, uint8[20][20] memory y) 
    pure
    public 
    returns (uint8[20][20] memory)  
    {
      x[i] = y[j];
      y[j][k] = value;
      assert (x[i][k] == value || x[j][k] == value);
      return x;
    }

}
