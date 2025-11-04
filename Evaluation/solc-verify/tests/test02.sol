pragma solidity ^0.5.0;

contract test20 {
  
/// @notice precondition i < 5
/// @notice precondition j < 5
/// @notice postcondition x[i][j] == value 
  function t20(uint8[5][5] memory x, uint8 i, uint8 j, uint8 value) 
    pure
    public 
    returns (uint8[5][5] memory)  
    {
        x[i][j] = value;
      return x;
    }

}