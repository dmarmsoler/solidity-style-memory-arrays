// SPDX-License-Identifier: MIT
// Memory test for assignment behavior (/certora/tutorials-code/memorytests/test05.sol)

pragma solidity ^0.8.25;


/**
 * @dev Implementation of assignment behavior of memroty variables in Solidity
 */
contract test17 {
   
    constructor() {
    }

// assign3 is a test function which verifies the value assignment to a 3D memory array (pointer) in Certora.
// assign3 accepts a 3D memory array of fixed size (x3), indeces (i3, j3 and k3) and value (y3).
// It returns memroty array, x3, after value assignment to a pointer operation.


function t17(uint8[10][10][10] memory x, uint8 i, uint8 j, uint8 k, uint8 y) 
    pure
    public 
    returns (uint8[10][10][10] memory)  
    {
      x [i][j][k] = y;
      return x;
    }

}