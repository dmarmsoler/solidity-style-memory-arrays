/**
 * 
 *
 * This is the example of pointer to pointer assignment for a 3D memory array with n=5. Please check rule `test06rule`.
 * Run using:
 *
 * certoraRun /home/asad/certora/tutorials-code/memorytests/test06.sol --verify test06:/home/asad/certora/tutorials-code/memorytests/test06spec.spec
 *
 * There should be no errors.
 */
 
 
 /**Test configurations: 
 *  Test behavior: Value to 3D memory array assignment 
 *  #Dimensions (D) : 3D
 *   Size       (n) : n = 5
 *   Single Aliasing: No
 *   Double Aliasing: No
 *            Result: (Verified) Failed to locate an internal function called 
  *           from test06-t06(uint8[5][5][5],uint8,uint8,uint8,uint8,uint8,uint8[5][5][5]): 
  *           Could not detect the internal function 
  *           test06.t06(uint8[5][5][5] x4, uint8 i4, uint8 j4, uint8 k4, uint8 l4, uint8 value4, uint8[5][5][5] y4) returns (uint8[5][5][5])
 *        path count: Low
 *      nonlinearity: Low
 * memory complexity: High
 *   loop complexity: High
 */

methods
{
    // When a function is not using the environment (e.g., `msg.sender`), it can be
    // declared as `envfree`
    function t06(uint8[5][5][5], uint8, uint8, uint8, uint8, uint8, uint8[5][5][5]) external returns (uint8[5][5][5] memory) envfree; 
}

/// @title Assignment must change the data at specified index in destination array 
rule test06rule() {


    uint8[5][5][5] dest_array31;
    uint8[5][5][5] source_array31;
    uint8[5][5][5] ret31;
    
    uint8 i31;
    uint8 j31;
    uint8 k31;
    uint8 l31;

    uint8 i310;
    uint8 j310;
    uint8 k310;
    uint8 l310;

    uint8 value31;

    ret31 = t06(dest_array31, i31, j31, k31, l31, value31, source_array31);
    
    require i31 < 5;
    require j31 < 5;    
    require k31 < 5;
    require l31 < 5;

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

