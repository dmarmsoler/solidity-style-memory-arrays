pragma solidity ^0.5.0;

contract test19 {
      
/// @notice precondition i < 5
/// @notice precondition j < 5
/// @notice precondition k < 5
/// @notice precondition l < 5
/// @notice precondition m < 5
/// @notice precondition n < 5
/// @notice precondition o < 5

/// @notice postcondition x[i][m][n][o] == value 

 function t19(uint8[5][5][5][5] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 m, uint8 n, uint8 o, uint8 value, uint8[5][5][5][5] memory y, uint8[5][5][5][5] memory z) 
    public 
    returns (uint8[5][5][5][5] memory)  
    {
      x[i] = z[j];
      z[j][k] = y[l][m];
      y[l][m][n][o]= value;
      return x;
    }
}