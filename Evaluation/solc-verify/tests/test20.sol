
pragma solidity ^0.5.0;

contract test20 {
 
/// @notice precondition i < 10
/// @notice precondition i < x.length
/// @notice precondition m < 10
/// @notice precondition m < x[i].length
/// @notice precondition n < 10

/// @notice precondition i < y.length
/// @notice precondition j < 10
/// @notice precondition j < y[i].length
/// @notice precondition k < 10
/// @notice precondition l < 10
/// @notice precondition l < z.length
/// @notice precondition m < 10
/// @notice precondition m < z[l].length
/// @notice precondition n < 10

/// @notice postcondition x[i][m][n] == value 

function t20(uint8[10][10][10] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 m, uint8 n, uint8 value, uint8[10][10][10] memory y, uint8[10][10][10] memory z) 
    public 
    returns (uint8[10][10][10] memory)  
    {
      x[i] = y[j];
      y[j][k] = z[l][m];
      z[l][m][n]= value;
      return x;
    }
}