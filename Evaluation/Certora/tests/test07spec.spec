/**
 * 
 *
 * This is the example of value to pointer assignment for a 3D memory array with n=10 (test05.sol). Please check rule `test17rule`.
 * Run using:
 *
 * certoraRun /home/asad/certora/tutorials-code/memorytests/test17.sol --verify test17:/home/asad/certora/tutorials-code/memorytests/test17spec.spec
 *
 * There should be no errors.
 */
 
 
 /**Test configurations: 
 *  Test behavior: Value to 3D memory array assignment 
 *  #Dimensions (D) : 3D
 *   Size       (n) : n = 10
 *   Single Aliasing: No 
 *   Double Aliasing: No
 *            Result: Time out
 *        path count: Low
 *      nonlinearity: Low
 * memory complexity: High
 *   loop complexity: High
 */
methods
{
    // When a function is not using the environment (e.g., `msg.sender`), it can be
    // declared as `envfree`
    function t17(uint8[10][10][10], uint8, uint8, uint8, uint8) external returns (uint8[10][10][10] memory) envfree;
}

/// @title Assignment must change the data at specified index in destination array 
rule test17rule() {


    uint8[10][10][10] dest_array3;
    uint8[10][10][10] ret3;
    
    uint8 i3;
    uint8 j3;
    uint8 k3;
    uint8 i31;
    uint8 j31;
    uint8 k31;
    uint8 value3;

    ret3 = t17(dest_array3, i3, j3, k3, value3);
    
    require i3 < 10;
    require j3 < 10;    
    require k3 < 10;
    require i31 < 10;
    require j31 < 10;    
    require k31 < 10;
    require i3 != i31;
    require j3 != j31;
    require k3 != k31;
/**@title return array contains the content of the source array
* 
*/
    assert ret3 [i3][j3][k3] == value3;
    assert ret3 [i31][j31][k31] == dest_array3 [i31][j31][k31];
}

