// SPDX-License-Identifier: MIT
// Memory test for assignment behavior (/certora/tutorials-code/memorytests/test11.sol)

pragma solidity ^0.8.25;


/**
 * @dev Implementation of assignment behavior of memroty variables in Solidity
 */
contract test11 {
   
    constructor() {
    }
// assign3dda is an implemntation of aliasing using three-dimensional fixed sized arrays.
// assign3dda accepts three arrays which are three dimensional arrays, respective indices and a value.
// The function performs a pointer-to-pointer operation on the given martrices and then assign value to the one of the arrays.
 function t11(uint8[5][5][5] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 m, uint8 n, uint8 value, uint8[5][5][5] memory y , uint8[5][5][5] memory z ) 
    pure
    public 
    returns (uint8[5][5][5] memory)  
    {
      x [i] = y [j];
      y [j][k] = z [l][m];
      z [l][m][n] = value;
      return x;
    }
}