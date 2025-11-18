// ./docker_solcmc examples test19.sol test19 60 eld -horn
// ./docker_solcmc examples test19.sol test19 60 z3

contract test19 {
   
    constructor() {
    }
    
function t19(uint8[5][5][5][5] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 m, uint8 n, uint8 o, uint8 value, uint8[5][5][5][5] memory y, uint8[5][5][5][5] memory z) 
    pure
    public 
    returns (uint8[5][5][5][5] memory)  
    {
      x[i] = z[j];
      z[j][k] = y[l][m];
      y[l][m][n][o]= value;
      assert (x[i][k][m][o] == value);
      return x;
    }
}
