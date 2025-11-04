/**
 * # Dummy Assignment Example
 *
 * This is the example of dummy assignment to memory array element. Please check rule `dummy2rule`.
 * Run using:
 *
 * certoraRun /home/asad/certora/tutorials-code/memorytests/dummyd2.sol --verify dummyd2:/home/asad/certora/tutorials-code/memorytests/dummyd2spec.spec
 *
 * There should be no errors.
 */
 
methods
{
    // When a function is not using the environment (e.g., `msg.sender`), it can be
    // declared as `envfree`
    function f(bool[1]) external returns (bool[1] memory) envfree;
}


rule dummy2rule() {


    bool[1] dummy_array;
    bool[1] ret;
    
   
    require dummy_array [0] == false ;
   
    
   //ret = f(bool[1][1]);
  
   assert ret[0] == false;
}