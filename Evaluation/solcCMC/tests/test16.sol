// ./docker_solcmc examples test16.sol test16 60 eld -horn
// ./docker_solcmc examples test16.sol test16 60 z3

contract test16 {
   
    constructor() {
    }

 function t16(uint8[10][10][10][10] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 m, uint8 value, uint8[10][10][10][10] memory y) 
    pure
    public 
    returns (uint8[10][10][10][10] memory)  
    {
      x[i] = y[j];
      y[j][k][l][m] = value;
      assert (x[i][k][l][m] == value);
      return x;
    }

}
