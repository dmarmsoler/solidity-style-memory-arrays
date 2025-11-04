// SPDX-License-Identifier: GPL-3.0
 
pragma solidity >=0.5.0;
 
contract test22 {
    /// @notice precondition x[0] == false
    /// @notice postcondition x[0] == false
    function t22(bool[1] memory x) public {
        bool[1] memory y;
        y[0] = true;
    }
}