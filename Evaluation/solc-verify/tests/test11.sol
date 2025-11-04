pragma solidity ^0.5.0;

contract test11 {

  
/// @notice precondition i < 5
/// @notice precondition i < x.length
/// @notice precondition j < 5
/// @notice precondition i < y.length
/// @notice precondition j < y[i].length
/// @notice precondition k < 5
/// @notice postcondition x[i][k] == value 
  function t11(uint8[5][5] memory x, uint8 i, uint8 j, uint8 k, uint8 value, uint8[5][5] memory y) 
    pure 
    public 
    returns (uint8[5][5] memory)  
    {
      x[i] = y[j];
      y[j][k] = value;
      return x;
    }

}