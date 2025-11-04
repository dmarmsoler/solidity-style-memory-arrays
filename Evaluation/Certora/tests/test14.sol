// SPDX-License-Identifier: MIT
// Memory test for assignment behavior (/certora/tutorials-code/memorytests/test08.sol)

pragma solidity ^0.8.25;


/**
 * @dev Implementation of assignment behavior of memroty variables in Solidity
 */
contract test08 {
   
    constructor() {
    }
// assign4dp2p is a test function which verifies the pointer to pointer array for 4D memory arrays in Certora.
// assign4dp2p accepts a 4D memory array of fixed size (x51), indeces (i51, j51, k51, l51 and m51) and value (value5).
// It returns memroty array, x51, after value to apointer assignment operation.


function t08(uint8[5][5][5][5] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 m, uint8 value, uint8[5][5][5][5] memory y ) 
    pure
    public 
    returns (uint8[5][5][5][5] memory)  
    {
      x [i] = y [j];
      y [j][k][l][m] = value;
      return x;
    }

}