// ./docker_solcmc examples test02.sol test02 60 eld -horn
// ./docker_solcmc examples test02.sol test02 60 z3

contract test02 {
   
    constructor() {
    }

  function t02(uint8[5][5] memory x, uint8 i, uint8 j, uint8 value) 
    pure
    public 
    returns (uint8[5][5] memory)  
    {
        x[i][j] = value;
        assert (x[i][j] == value);
      return x;
    }

}
