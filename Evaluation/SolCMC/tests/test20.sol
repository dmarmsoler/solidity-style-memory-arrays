
  // ./docker_solcmc examples test20.sol test20 60 eld -horn
  // ./docker_solcmc examples test20.sol test20 60 z3

contract test20 {
   
    constructor() {
    }

function t20(uint8[10][10][10] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 m, uint8 n, uint8 value, uint8[10][10][10] memory y, uint8[10][10][10] memory z) 
    public 
    returns (uint8[10][10][10] memory)  
    {
      x[i] = y[j];
      y[j][k] = z[l][m];
      z[l][m][n]= value;
      assert (x[i][k][n] == value);
      return x;
    }
}