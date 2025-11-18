// ./docker_solcmc examples test22.sol test22 60 eld -horn
// ./docker_solcmc examples test22.sol test22 60 z3
// SPDX-License-Identifier: GPL-3.0
 
 
contract test22 {
   
    constructor() {
    }

    function t22(bool[1] memory x) pure public {
      require (x[0] == false);
        bool[1] memory y;
        y[0] = true;
        assert (x[0] == false);

    }
}
