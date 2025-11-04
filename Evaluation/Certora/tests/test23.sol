pragma solidity >=0.8.25;
 
contract dummyd1 {
   
    function 
    f(bool[1][1] memory x) 
    pure 
    public 
    returns (bool[1][1] memory)  
    {
        bool[1][1] memory y;
        y[0][0] = true;
        return x;
    }
}