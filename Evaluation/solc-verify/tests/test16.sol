pragma solidity ^0.5.0;

contract test16 {
    
/// @notice precondition i < 10
/// @notice precondition i < x.length
/// @notice precondition j < 10
/// @notice precondition j < x[i].length
/// @notice precondition k < 10
/// @notice precondition k < x[i][j].length
/// @notice precondition l < 10
/// @notice precondition l < x[i][j][k].length
/// @notice precondition m < 10
/// @notice precondition i < y.length
/// @notice precondition j < y[i].length
/// @notice precondition k < y[i][j].length
/// @notice precondition l < y[i][j][k].length

/// @notice postcondition x[i][k][l][m] == value 
 function t16(uint8[10][10][10][10] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 m, uint8 value, uint8[10][10][10][10] memory y) 
    pure
    public 
    returns (uint8[10][10][10][10] memory)  
    {
      x[i] = y[j];
      y[j][k][l][m] = value;
      return x;
    }

}