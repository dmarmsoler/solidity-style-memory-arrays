
/**
 * # v2p Example
 *
 * This is the example of value to pointer assignment. Please check rule `test10rule`.
 * Run using:
 *
 * certoraRun /home/asad/certora/tutorials-code/memorytests/test10.sol --verify test10:/home/asad/certora/tutorials-code/memorytests/test10spec.spec
 *
 * There should be no errors.
 */
 
 /**Test configurations: 
 *  Test behavior: 2D memory array single Aliasing followed by assignment 
 *  #Dimensions (D) : 2D
 *   Size       (n) : n = 20
 *   Single Aliasing: Yes
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
    function t10(uint8[20][20], uint8, uint8, uint8, uint8, uint8 [20][20]) external returns (uint8[20][20] memory) envfree;
  }

/// @title Assignment must change the data at specified index in destination array 
rule test10rule() {


    uint8[20][20] dest_array3;
    uint8[20][20] ret3;
    
    uint8[20][20] source_array3;
    uint8 i3;
    uint8 j3;
    uint8 k3;
    uint8 value3;

    ret3 = t10(dest_array3, i3, j3, k3, value3, source_array3);
    require i3 < 20;
    require j3 < 20;
    require k3 < 20;

    require j3 != i3;
    
   
/**@title return array contains the content of the source array
* 
*/
// Return/dest array contains values assigned to source array at specified index
    assert ret3 [i3][k3] == value3;
// Retrun/dest array comparison for all other values which do not lie on the value3 index

    assert ret3 [j3][k3] == dest_array3[j3][k3];
}