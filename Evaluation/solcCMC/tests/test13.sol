// ./docker_solcmc examples test13.sol test13 60 eld -horn
// ./docker_solcmc examples test13.sol test13 60 z3
contract test13 {
   
    constructor() {
    }

 function t13(uint8[5][5][5] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 value, uint8[5][5][5] memory y) 
    pure
    public 
    returns (uint8[5][5][5] memory)  
    {
      x[i] = y[j];
      y[j][k][l] = value;
      assert (x[j][k][l] == value || x[i][k][l] == value);
      return x;
    }

}
