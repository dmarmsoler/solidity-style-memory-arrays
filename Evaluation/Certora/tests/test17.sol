
    // SPDX-License-Identifier: MIT
// Memory test for assignment behavior (/certora/tutorials-code/memorytests/test14.sol)

pragma solidity ^0.8.25;


/**
 * @dev Implementation of assignment behavior of memroty variables in Solidity
 */
contract test14 {
   
    constructor() {
    }
// assigndyvtp is a function that accepts a dynamic memory array, performs an value-to-pointer assignment  operations and rerutrns 
 // the dynamic array. 
 // The function is design to test Certora verification of dynamic arrays

 function t14(uint8[][] memory x, uint8 i, uint8 j, uint8 k, uint8 value, uint8[][] memory y ) 
    pure
    public 
    returns (uint8[][] memory)  
    {
     x [i] = y [j];
      y [j][k] = value;
      return x;
    }

}
