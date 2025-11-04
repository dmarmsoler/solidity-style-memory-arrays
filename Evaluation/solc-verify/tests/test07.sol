pragma solidity ^0.5.0;

contract test17 {

/// @notice precondition i < 10
/// @notice precondition j < 10
/// @notice precondition k < 10
/// @notice precondition x[i][j][k] != value
/// @notice postcondition x[i][j][k] == value
function t17(uint8[10][10][10] memory x, uint8 i, uint8 j, uint8 k, uint8 value) 
    pure
    public 
    returns (uint8[10][10][10] memory)  
    {
      x[i][j][k] = value;
      return x;
    }

}