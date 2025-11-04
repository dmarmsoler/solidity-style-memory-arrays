/**
 * 
 *
 * This is the example of pointer to pointer assignment for a 3D memory array with n=10 (test06.sol). Please check rule `test18rule`.
 * Run using:
 *
 * certoraRun /home/asad/certora/tutorials-code/memorytests/test18.sol --verify test18:/home/asad/certora/tutorials-code/memorytests/test18spec.spec
 *
 * There should be no errors.
 */
 
 
 /**Test configurations: 
 *  Test behavior: Value to 3D memory array assignment 
 *  #Dimensions (D) : 3D
 *   Size       (n) : n = 10
 *   Single Aliasing: Yes
 *   Double Aliasing: No
 *            Result: Problem
 *             error: Prover out of memory
 */

methods
{
    // When a function is not using the environment (e.g., `msg.sender`), it can be
    // declared as `envfree`
    function t18(uint8[10][10][10] , uint8, uint8, uint8, uint8, uint8, uint8[10][10][10])  external returns (uint8[10][10][10]  memory) envfree; 
}

/// @title Assignment must change the data at specified index in destination array 
rule test18rule() {


    uint8[10][10][10]  dest_array31;
    uint8[10][10][10]  source_array31;
    uint8[10][10][10]  ret31;
    
    uint8 i31;
    uint8 j31;
    uint8 k31;
    uint8 l31;

    uint8 i310;
    uint8 j310;
    uint8 k310;
    uint8 l310;

    uint8 value31;

    ret31 = t18(dest_array31, i31, j31, k31, l31, value31, source_array31);
    
    require i31 < 10;
    require j31 < 10;    
    require k31 < 10;
    require l31 < 10;

   // require i310 < 5;
   // require j310 < 5;    
   // require k310 < 5;
   // require l310 < 5;

    
  // require i31 != j31;
   // require j31 != j310;
   // require k31 != k310;
   // require l31 != l310;

/**@title return destination array contains the copied content of the source array at specified indeces
* 
*/
    assert ret31 [i31][k31][l31] == value31;

/**@title return destination array content is preserved except the one copied to destination array
* 
*/
  //  assert ret31 [j31][k31][l31] == dest_array31 [j31][k31][l31];
}

