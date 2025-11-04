
// ./docker_solcmc examples test18.sol test18 60 eld -horn
// ./docker_solcmc examples test18.sol test18 60 z3

contract test18 {
   
    constructor() {
    }

 function t18(uint8[5][5][5] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 m, uint8 n, uint8 value, uint8[5][5][5] memory y, uint8[5][5][5] memory z) 
    pure
    public 
    returns (uint8[5][5][5] memory)  
    {
      x[i] = y[j];
      y[j][k] = z[l][m];
      z[l][m][n]= value;
      assert (x[i][k][n] == value );
      return x;
    }
}