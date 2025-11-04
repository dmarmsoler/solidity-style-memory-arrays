// SPDX-License-Identifier: MIT
// Memory test for assignment behavior (/certora/tutorials-code/memorytests/test18.sol)

pragma solidity ^0.8.25;


/**
 * @dev Implementation of assignment behavior of memroty variables in Solidity
 */
contract test18 {
   
    constructor() {
    }

// assign31 is a test function which verifies the pointer to pointer array for 3D memory arrays in Certora.
// assign31 accepts a 3D memory array of fixed size (x4), indeces (i4, j4, k4 and l4), value (value4) and y4 3D memory.
// It returns memroty array, x3, after pointer to a pointer and value assignment operation, respectively.


 function t18(uint8[10][10][10] memory x, uint8 i, uint8 j, uint8 k, uint8 l, uint8 value, uint8[10][10][10] memory y) 
    pure
    public 
    returns (uint8[10][10][10] memory)  
    {
      x [i] = y [j];
      y [j][k][l] = value;
      return x;
    }

}