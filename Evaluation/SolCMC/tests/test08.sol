// ./docker_solcmc examples test08.sol test08 60 eld -horn
// ./docker_solcmc examples test08.sol test08 60 z3

contract test08 {
   
    constructor() {
    }

function t08(uint8[10][10][10][10] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 value) 
    pure
    public 
    returns (uint8[10][10][10][10] memory)  
    {
      x[i][j][k][l] = value;
      assert (x[i][j][k][l] == value);
      return x;
    }


}
