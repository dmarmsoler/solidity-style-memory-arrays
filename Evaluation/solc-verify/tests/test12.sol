pragma solidity ^0.5.0;

contract test12 {

  
/// @notice precondition i < 20
/// @notice precondition i < x.length
/// @notice precondition j < 20
/// @notice precondition i < y.length
/// @notice precondition j < y[i].length
/// @notice precondition k < 20
/// @notice postcondition x[i][k] == value 
  function t12(uint8[20][20] memory x, uint8 i, uint8 j, uint8 k, uint8 value, uint8[20][20] memory y) 
    pure
    public 
    returns (uint8[20][20] memory)  
    {
      x[i] = y[j];
      y[j][k] = value;
      return x;
    }

}