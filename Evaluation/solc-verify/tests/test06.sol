pragma solidity ^0.5.0;

contract test07 {
    
/// @notice precondition i < 5
/// @notice precondition i < x.length
/// @notice precondition j < 5
/// @notice precondition j < x[i].length
/// @notice precondition k < 5
/// @notice precondition k < x[i][j].length
/// @notice precondition l < 5
/// @notice precondition l < x[i][j][l].length
/// @notice postcondition x[i][j][k][l] == value 
function t07(uint8[5][5][5][5] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 value) 
    pure 
    public 
    returns (uint8[5][5][5][5] memory)  
    {
      x[i][j][k][l] = value;
      return x;
    }


}