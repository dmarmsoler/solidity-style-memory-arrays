// ./docker_solcmc examples test06.sol test06 60 eld -horn
// ./docker_solcmc examples test06.sol test06 60 z3

contract test06 {
   
    constructor() {
    }

function t06(uint8[5][5][5][5] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 value) 
    pure
    public 
    returns (uint8[5][5][5][5] memory)  
    {
      x[i][j][k][l] = value;
      assert(x[i][j][k][l] == value);
      return x;
    }


}
