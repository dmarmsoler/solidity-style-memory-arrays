
/**
 * # v2p Example
 *
 * This is the example of value to pointer assignment. Please check rule `test24rule`.
 * Run using:
 *
 * certoraRun /home/asad/certora/tutorials-code/memorytests/test24.sol --verify test24:/home/asad/certora/tutorials-code/memorytests/test24spec.spec
 *
 * There should be no errors.
 */
 
 
 /**Test configurations: 
 *  Test behavior: 4D memory array single Aliasing followed by assignment 
 *  #Dimensions (D) : 4D
 *   Size       (n) : n = 10
 *   Single Aliasing: No
 *   Double Aliasing: Yes
 *            Result: Problem
 *        path count: Low
 *      nonlinearity: Low
 * memory complexity: High
 *   loop complexity: High
 */

methods
{
    // When a function is not using the environment (e.g., `msg.sender`), it can be
    // declared as `envfree`
    function t24(uint8[10][10][10][10], uint8, uint8, uint8, uint8, uint8, uint8, uint8, uint8, uint8[10][10][10][10], uint8[10][10][10][10]) 
             external 
             returns (uint8[10][10][10][10] memory) 
             envfree; 
 
  }

/// @title Assignment must change the data at specified index in destination array 
rule test24rule() {


    uint8[10][10][10][10] dest_array3;
    uint8[10][10][10][10] ret3;
    uint8[10][10][10][10] t_array3;
    uint8[10][10][10][10] source_array3;

    uint8 i3;
    uint8 j3;
    uint8 k3;
    uint8 l3;
    uint8 m3;
    uint8 n3;
    uint8 o3;
    uint8 value3;

    ret3 = t24(dest_array3, i3, j3, k3, l3, m3, n3, o3, value3, source_array3, t_array3);
    require i3 < 10;
    require j3 < 10;
    require k3 < 10;
    require l3 < 10;
    require m3 < 10;
    require n3 < 10;
   require o3 < 10;
   
/**@title return array contains the content of the destination array
* 
*/
// Return/dest array contains values assigned to destination array at specified index
    assert ret3 [i3][k3][n3][o3] == value3;
}