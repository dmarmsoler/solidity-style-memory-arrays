
     // ./docker_solcmc examples test17.sol test17 60 eld -horn
     // ./docker_solcmc examples test17.sol test17 60 z3

contract test17 {
   
    constructor() {
    }

 function t17(uint8[][] memory x, uint8 i, uint8 j, uint8 k, uint8 value, uint8[][] memory y) 
    pure 
    public 
    returns (uint8[][] memory)  
    {
     x[i] = y[j];
      y[j][k] = value;
      assert (x[i][k] == value);
      return x;
    }

}
