// ./docker_solcmc examples test05.sol test05 60 eld -horn
// ./docker_solcmc examples test05.sol test05 60 z3


contract test05 {
   
    constructor() {
    }

function t05(uint8[5][5][5] memory x, uint8 i, uint8 j, uint8 k, uint8 y) 
    pure
    public 
    returns (uint8[5][5][5] memory)  
    {
      x[i][j][k] = y;
      assert (x[i][j][k] == y);
      return x;
    }

}
