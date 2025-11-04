pragma solidity ^0.5.0;

contract test15 {
    
/// @notice precondition i < 10
/// @notice precondition i < x.length
/// @notice precondition j < 10
/// @notice precondition j < x[i].length
/// @notice precondition k < 10
/// @notice precondition k < x[i][j].length
/// @notice precondition i < y.length
/// @notice precondition j < y[i].length
/// @notice precondition k < y[i][j].length
/// @notice postcondition x[i][k][l] == value 

 function t15(uint8[10][10][10] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 value, uint8[10][10][10] memory y) 
    public 
    returns (uint8[10][10][10] memory)  
    {
      x[i] = y[j];
      y[j][k][l] = value;
      return x;
    }

}