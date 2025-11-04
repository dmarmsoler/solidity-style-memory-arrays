// SPDX-License-Identifier: MIT
// Memory test for assignment behavior (/certora/tutorials-code/memorytests/test10.sol)

pragma solidity ^0.8.25;


/**
 * @dev Implementation of assignment behavior of memory variables in Solidity
 */
contract test10 {
   
    constructor() {
    }
// assign2dp2p2 is an implementation of aliasing using two-dimensional fixed sized array.
// assign6 accepts two dimensional fixed sized arrays , their respective indices and value.
// The test invovlves the pointer-to-pointe assignment followed by the value-to-pointer assignemnt.

  function t10(uint8[20][20] memory x, uint8 i, uint8 j, uint8 k, uint8 value, uint8[20][20] memory y ) 
    pure
    public 
    returns (uint8[20][20] memory)  
    {
      x [i] = y [j];
      y [j][k] = value;
      return x;
    }

}