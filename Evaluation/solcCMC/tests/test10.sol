// ./docker_solcmc examples test10.sol test10 60 eld -horn
// ./docker_solcmc examples test10.sol test10 60 z3

contract test10 {
   
    constructor() {
    }

function t10(uint8[][] memory x, uint8 i, uint8 j, uint8 value) 
    pure
    public 
    returns (uint8[][] memory)  
    {
      x[i][j] = value;
      assert (x[i][j] == value);
      return x;
    }

}
