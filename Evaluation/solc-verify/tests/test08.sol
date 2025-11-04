pragma solidity ^0.5.0;

contract test19 {
    
/// @notice precondition i < 10
/// @notice precondition i < x.length
/// @notice precondition j < 10
/// @notice precondition j < x[i].length
/// @notice precondition k < 10
/// @notice precondition k < x[i][j].length
/// @notice precondition l < 10
/// @notice precondition l < x[i][j][l].length
/// @notice postcondition x[i][j][k][l] == value 
function t19(uint8[10][10][10][10] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 value) 
    public 
    returns (uint8[10][10][10][10] memory)  
    {
      x[i][j][k][l] = value;
      return x;
    }


}