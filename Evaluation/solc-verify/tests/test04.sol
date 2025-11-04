pragma solidity ^0.5.0;

contract test21 {

/// @notice precondition i < 20
/// @notice precondition j < 20
/// @notice postcondition x[i][j] == value 
  function t21(uint8[20][20] memory x, uint8 i, uint8 j, uint8 value) 
    public 
    returns (uint8[20][20] memory)  
    {
        x[i][j] = value;
      return x;
    }

}