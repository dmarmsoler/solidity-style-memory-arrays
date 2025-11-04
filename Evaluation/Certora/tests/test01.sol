// SPDX-License-Identifier: MIT
// Memory test for assignment behavior 

pragma solidity ^0.8.25;


/**
 * @dev Implementation of assignment behavior of memroty variables in Solidity
 */
contract test01 {
   
   constructor() {
   }

   function t01(uint8[5] memory x, uint8 i, uint8 y) 
      pure
      public 
      returns (uint8[5] memory) {
      x[i] = y;
      return x;
    }

}