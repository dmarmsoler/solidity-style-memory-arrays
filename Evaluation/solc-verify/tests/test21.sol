pragma solidity ^0.5.0;

contract test21 {
    
/// @notice precondition i < 10
/// @notice precondition j < 10
/// @notice precondition k < 10
/// @notice precondition l < 10
/// @notice precondition m < 10
/// @notice precondition n < 10
/// @notice precondition o < 10

/// @notice postcondition x[i][m][n][o] == value 

 function t21(uint8[10][10][10][10] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 m, uint8 n, uint8 o, uint8 value, uint8[10][10][10][10] memory y, uint8[10][10][10][10] memory z) 
    pure
    public 
    returns (uint8[10][10][10][10] memory)  
    {
      x[i] = z[j];
      z[j][k] = y[l][m];
      y[l][m][n][o]= value;
      return x;
    }
}