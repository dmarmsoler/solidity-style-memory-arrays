// ./docker_solcmc examples test15.sol test15 60 eld -horn
// ./docker_solcmc examples test15.sol test15 60 z3

contract test15 {
   
    constructor() {
    }


 function t15(uint8[10][10][10] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 value, uint8[10][10][10] memory y) 
    pure 
    public 
    returns (uint8[10][10][10] memory)  
    {
      x[i] = y[j];
      y[j][k][l] = value;
      assert (x[i][k][l] == value);
      return x;
    }

}
