// docker run --rm -v C:\Users\aa1558\contracts:/contracts solc-verify:latest '/contracts/test01.sol'

pragma solidity ^0.5.0;
contract test01 {

  
/// @notice precondition i < 5
/// @notice precondition i < x.length
/// @notice postcondition x[i] == y
    function t01(uint8[5] memory x, uint8 i, uint8 y) 
        pure
        public 
        returns (uint8[5] memory)  
    {
        x[i] = y;
        return x;
    }
}