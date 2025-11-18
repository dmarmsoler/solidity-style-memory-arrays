// ./docker_solcmc examples test23.sol test23 60 eld -horn
// ./docker_solcmc examples test23.sol test23 60 z3
// SPDX-License-Identifier: GPL-3.0
 
 
contract test23 {
   
    constructor() {
    }

    function t23(bool[1][1] memory x) pure public {
      require (x[0][0] == false);
        bool[1][1] memory y;
        y[0][0] = true;
        assert (x[0][0] == false);

    }
}
