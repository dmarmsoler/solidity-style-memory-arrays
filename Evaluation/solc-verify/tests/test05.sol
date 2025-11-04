pragma solidity ^0.5.0;

contract test05 {

/// @notice precondition i < 5
/// @notice precondition j < 5
/// @notice precondition k < 5
/// @notice precondition x[i][j][k] != value
/// @notice postcondition x[i][j][k] == value
function t05(uint8[5][5][5] memory x, uint8 i, uint8 j, uint8 k, uint8 value) 
    pure 
    public 
    returns (uint8[5][5][5] memory)  
    {
      x[i][j][k] = value;
      return x;
    }

}