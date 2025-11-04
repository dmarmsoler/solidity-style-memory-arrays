// SPDX-License-Identifier: MIT
// Memory test for assignment behavior (/certora/tutorials-code/memorytests/test02.sol)

pragma solidity ^0.8.25;


/**
 * @dev Implementation of assignment behavior of memroty variables in Solidity
 */
contract test02 {
   
    constructor() {
    }

// assign2 function is similar to assign1.
// Only difference is size of the fixed-sized array.
// assign2 is designed to assess the affect of size of the array in relation to verification effort in Certora

    function t02(uint8[20] memory x, uint8 i, uint8 y) 
    pure
    public 
    returns (uint8[20] memory)  
    {
      x[i] = y;
      return x;
    }
}