// ./docker_solcmc examples test07.sol test07 60 eld -horn
// ./docker_solcmc examples test07.sol test07 60 z3

contract test07 {
   
    constructor() {
    }


function t07(uint8[10][10][10] memory x, uint8 i, uint8 j, uint8 k, uint8 y) 
    pure
    public 
    returns (uint8[10][10][10] memory)  
    {
      x[i][j][k] = y;
      assert (x[i][j][k] == y);
      return x;
    }

}
