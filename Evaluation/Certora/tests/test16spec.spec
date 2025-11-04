/**
 * 
 *
 * This is the example of pointer to pointer assignment for a 3D memory array with n=10. Please check rule `test22rule`.
 * Run using:
 *
 * certoraRun /home/asad/certora/tutorials-code/memorytests/test22.sol --verify test22:/home/asad/certora/tutorials-code/memorytests/test22spec.spec
 *
 * There should be no errors.
 */
 
 
 /**Test configurations: 
 *  Test behavior: pointer to pointer assignment behavior of 4D memory arrays 
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
    function t22(uint8[10][10][10][10] , uint8, uint8, uint8, uint8, uint8, uint8, uint8[10][10][10][10])  external returns (uint8[10][10][10][10]  memory) envfree; 
}

/// @title Assignment must change the data at specified index in destination array 
rule test22rule() {


    uint8[10][10][10][10]  dest_array31;
    uint8[10][10][10][10]  source_array31;
    uint8[10][10][10][10]  ret31;
    
    uint8 i31;
    uint8 j31;
    uint8 k31;
    uint8 l31;
    uint8 m31;

    uint8 value31;

    ret31 = t22(dest_array31, i31, j31, k31, l31, m31, value31, source_array31);
    
    require i31 < 10;
    require j31 < 10;    
    require k31 < 10;
    require l31 < 10;
    require m31 < 10;

/**@title return destination array contains the copied content of the source array at specified indeces
* 
*/
    assert ret31 [i31][k31][l31][m31] == value31;
}

