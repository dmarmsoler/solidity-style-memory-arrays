/**
 * 
 *
 * This is the example of value to pointer assignment for a 3D memory array with n=5. Please check rule `test05rule`.
 * Run using:
 *
 * certoraRun /home/asad/certora/tutorials-code/memorytests/test05.sol --verify test05:/home/asad/certora/tutorials-code/memorytests/test05spec.spec
 *
 * There should be no errors.
 */
 
 
 /**Test configurations: 
 *  Test behavior: Value to 3D memory array assignment 
 *  #Dimensions (D) : 3D
 *   Size       (n) : n = 5
 *   Single Aliasing: No 
 *   Double Aliasing: No
 *            Result: pass
 */
methods
{
    // When a function is not using the environment (e.g., `msg.sender`), it can be
    // declared as `envfree`
    function t05(uint8[5][5][5], uint8, uint8, uint8, uint8) external returns (uint8[5][5][5] memory) envfree;
}

/// @title Assignment must change the data at specified index in destination array 
rule test05rule() {


    uint8[5][5][5] dest_array3;
    uint8[5][5][5] ret3;
    
    uint8 i3;
    uint8 j3;
    uint8 k3;
    uint8 i31;
    uint8 j31;
    uint8 k31;
    uint8 value3;

    ret3 = t05(dest_array3, i3, j3, k3, value3);
    
    require i3 < 5;
    require j3 < 5;    
    require k3 < 5;
    require i31 < 5;
    require j31 < 5;    
    require k31 < 5;
    require i3 != i31;
    require j3 != j31;
    require k3 != k31;
/**@title return array contains the content of the source array
* 
*/
    assert ret3 [i3][j3][k3] == value3;
    assert ret3 [i31][j31][k31] == dest_array3 [i31][j31][k31];
}

