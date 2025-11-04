/**
 * 
 *
 * This is the example of value to pointer assignment for a 4D memory array with n=10 (test07.sol). Please check rule `test19rule`.
 * Run using:
 *
 * certoraRun /home/asad/certora/tutorials-code/memorytests/test19.sol --verify test19:/home/asad/certora/tutorials-code/memorytests/test19spec.spec
 *
 * There should be no errors.
 */
 
 
 /**Test configurations: 
 *  Test behavior: Value to 4D memory array assignment 
 *  #Dimensions (D) : 4D
 *   Size       (n) : n = 10
 *   Single Aliasing: No
 *   Double Aliasing: No
 *            Result: Problem
 */

methods
{
    // When a function is not using the environment (e.g., `msg.sender`), it can be
    // declared as `envfree`
    function t19(uint8[10][10][10][10], uint8, uint8, uint8, uint8, uint8) external returns (uint8[10][10][10][10] memory) envfree; 
}

/// @title Assignment must change the data at specified index in destination array 
rule test19rule() {


    uint8[10][10][10][10] dest_array4;
    uint8[10][10][10][10] ret4;
    
    uint8 i4;
    uint8 j4;
    uint8 k4;
    uint8 l4;

    uint8 i40;
    uint8 j40;
    uint8 k40;
    uint8 l40;

    uint8 value4;

    ret4 = t19(dest_array4, i4, j4, k4, l4, value4);
    
    require i4 < 10;
    require j4 < 10;    
    require k4 < 10;
    require l4 < 10;

   // require i40 < 5;
   // require j40 < 5;    
   // require k40 < 5;
   // require l40 < 5;

    
    //require i4 != i40;
    //require j4 != j40;
    //require k4 != k40;
    //require l4 != l40;

/**@title return destination array contains the copied content of the source array at specified indeces
* 
*/
    assert ret4 [i4][j4][k4][l4] == value4;

/**@title return destination array content is preserved except the one copied to destination array
* 
*/
  //  assert ret4 [i40][j40][k40][l40] == dest_array4 [i40][j40][k40][l40];
}


