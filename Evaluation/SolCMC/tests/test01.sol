//./docker_solcmc examples test01.sol test01 60 eld -horn
//./docker_solcmc examples test01.sol test01 60 z3
contract test01 {
   
    constructor() {
    }

 function  t01(uint8[5] memory x, uint8 i, uint8 y) 
    pure
    public 
    returns (uint8[5] memory)  
    {
      x[i] = y;
       assert (x[i] == y);
      return x;
    }

}