// SPDX-License-Identifier: MIT
// Memory test for assignment behavior (/certora/tutorials-code/memorytests/test05.sol)

pragma solidity ^0.8.25;


/**
 * @dev Implementation of assignment behavior of memroty variables in Solidity
 */
contract test05 {
   
    constructor() {
    }

// assign3 is a test function which verifies the value assignment to a 3D memory array (pointer) in Certora.
// assign3 accepts a 3D memory array of fixed size (x3), indeces (i3, j3 and k3) and value (y3).
// It returns memroty array, x3, after value assignment to a pointer operation.


function t05(uint8[5][5][5] memory x, uint8 i, uint8 j, uint8 k, uint8 y ) 
    public 
    returns (uint8[5][5][5] memory)  
    {
      x [i][j][k] = y;
      return x;
    }

}
/*
asad@5CG415590F:/mnt/c/Users/aa1558/leonardoalt-cav_2022_artifact-64b7aab$ ./docker_solcmc examples test12.sol test12 60 eld -horn
//### Running with solver eld
//### Entire output:
{
  errors: [
    {
      component: 'general',
      errorCode: '2018',
      formattedMessage: 'Warning: Function state mutability can be restricted to pure\n' +
        '  --> fileName:10:1:\n' +
        '   |\n' +
        '10 | function t12(uint8[10][10][10] memo ... y91, uint8[10][10][10] memory z91) \n' +
        '   | ^ (Relevant source part starts here and spans across multiple lines).\n' +
        '\n',
      message: 'Function state mutability can be restricted to pure',
      severity: 'warning',
      sourceLocation: [Object],
      type: 'Warning'
    },
    {
      component: 'general',
      errorCode: '6328',
      formattedMessage: 'Warning: CHC: Assertion violation happens here.\n' +
        'Counterexample:\n' +
        '\n' +
        'i91 = 255\n' +
        'j91 = 255\n' +
        'k91 = 255\n' +
        'l91 = 255\n' +
        'm91 = 0\n' +
        'n91 = 0\n' +
        'value91 = 1\n' +
        '\n' +
        'Transaction trace:\n' +
        'test12.constructor()\n' +
        'test12.t12(x91, 255, 255, 255, 255, 0, 0, 1, y91, z91)\n' +
        '  --> fileName:17:7:\n' +
        '   |\n' +
        '17 |       assert (x91[i91][k91][n91] == value91);\n' +
        '   |       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n' +
        '\n',
      message: 'CHC: Assertion violation happens here.\n' +
        'Counterexample:\n' +
        '\n' +
        'i91 = 255\n' +
        'j91 = 255\n' +
        'k91 = 255\n' +
        'l91 = 255\n' +
        'm91 = 0\n' +
        'n91 = 0\n' +
        'value91 = 1\n' +
        '\n' +
        'Transaction trace:\n' +
        'test12.constructor()\n' +
        'test12.t12(x91, 255, 255, 255, 255, 0, 0, 1, y91, z91)',
      severity: 'warning',
      sourceLocation: [Object],
      type: 'Warning'
    }
  ],
  sources: { fileName: { id: 0 } }
}
//### End output
//##### Solver eld cex:
Warning: CHC: Assertion violation happens here.
Counterexample:

i91 = 255
j91 = 255
k91 = 255
l91 = 255
m91 = 0
n91 = 0
value91 = 1

Transaction trace:
test12.constructor()
test12.t12(x91, 255, 255, 255, 255, 0, 0, 1, y91, z91)
  --> fileName:17:7:
   |
17 |       assert (x91[i91][k91][n91] == value91);
   |       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


//##### End counterexample


//####### Final solving and time report:
Solver eld solved in 4017.464345999062ms
*/