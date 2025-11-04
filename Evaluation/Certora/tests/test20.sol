
    // SPDX-License-Identifier: MIT
// Memory test for assignment behavior (/certora/tutorials-code/memorytests/test12.sol)

pragma solidity ^0.8.25;


/**
 * @dev Implementation of assignment behavior of memroty variables in Solidity
 */
contract test12 {
   
    constructor() {
    }
// test12.sol is same as test11.
// Only difference is the size of the given matrices to guage the effect on the verification effort in Certora.
function t12(uint8[10][10][10] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 m, uint8 n, uint8 value, uint8[10][10][10] memory y, uint8[10][10][10] memory z ) 
    pure
    public 
    returns (uint8[10][10][10] memory)  
    {
      x [i] = y [j];
      y [j][k] = z [l][m];
      z [l][m][n]= value;
      return x;
    }
}