// ./docker_solcmc examples test04.sol test04 60 eld -horn
// ./docker_solcmc examples test04.sol test04 60 z3

contract test04 {
   
    constructor() {
    }

  function t04(uint8[20][20] memory x, uint8 i, uint8 j, uint8 value) 
    pure
    public 
    returns (uint8[20][20] memory)  
    {
        x[i][j] = value;
        assert (x[i][j] == value);
      return x;
    }

}
