// ./docker_solcmc examples test14.sol test14 60 eld -horn
// ./docker_solcmc examples test14.sol test14 60 z3


contract test14 {
   
    constructor() {
    }


function t14(uint8[5][5][5][5] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 m, uint8 value, uint8[5][5][5][5] memory y) 
    pure
    public 
    returns (uint8[5][5][5][5] memory)  
    {
      x[i] = y[j];
      y[j][k][l][m] = value;
      assert(x[i][k][l][m] == value || x[j][k][l][m] == value);
      return x;
    }

}
