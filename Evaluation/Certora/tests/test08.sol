// SPDX-License-Identifier: MIT
// Memory test for assignment behavior (/certora/tutorials-code/memorytests/test19.sol)

pragma solidity ^0.8.25;


/**
 * @dev Implementation of assignment behavior of memroty variables in Solidity
 */
contract test19 {
   
    constructor() {
    }

// assign4dvp is a test function which verifies the assignment to pointer array for 4D memory arrays in Certora.
// assign4dvp accepts a 4D memory array of fixed size (x5), indeces (i5, j5, k5 and l5) and value (value5).
// It returns memroty array, x5, after value to apointer assignment operation.

function t19(uint8[10][10][10][10] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 value) 
    pure
    public 
    returns (uint8[10][10][10][10] memory)  
    {
      x [i][j][k][l] = value;
      return x;
    }


}