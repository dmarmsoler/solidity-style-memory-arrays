
// ./docker_solcmc examples test11.sol test11 60 eld -horn
// ./docker_solcmc examples test11.sol test11 60 z3

contract test11 {
   
    constructor() {
    }

  function t11(uint8[5][5] memory x, uint8 i, uint8 j, uint8 k, uint8 value, uint8[5][5] memory y) 
    pure
    public 
    returns (uint8[5][5] memory)  
    {
      x[i] = y[j];
      y[j][k] = value;
      assert (x[j][k] == value || x[i][k] == value );
      return x;
    }

}
