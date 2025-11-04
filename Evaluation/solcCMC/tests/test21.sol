// ./docker_solcmc examples test21.sol test21 60 eld -horn
// ./docker_solcmc examples test21.sol test21 60 z3

contract test21 {
   
    constructor() {
    }

function t21(uint8[10][10][10][10] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 m, uint8 n, uint8 o, uint8 value, uint8[10][10][10][10] memory y, uint8[10][10][10][10] memory z) 
    pure
    public 
    returns (uint8[10][10][10][10] memory)  
    {
      x[i] = z[j];
      z[j][k] = y[l][m];
      y[l][m][n][o]= value;
      assert (x[i][k][m][o] == value);
      return x;
    }
}