//  docker run --rm -v C:\Users\aa1558\contracts:/contracts solc-verify:latest '/contracts/test23.sol'
pragma solidity >=0.5.0;
 
contract test23 {
    /// @notice precondition x[0][0] == false
    /// @notice postcondition x[0][0] == false
    function t23(bool[1][1] memory x) public {
        bool[1][1] memory y;
        y[0][0] = true;
    }
}