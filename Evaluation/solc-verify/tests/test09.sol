pragma solidity ^0.5.0;

contract test13 {

/// @notice precondition i < x.length
/// @notice postcondition x[i] == y

 function t13(uint8[] memory x, uint8 i, uint8 y) 
    pure 
    public 
    returns (uint8[] memory)  
    {
      x[i] = y;
      return x;
    }
}