
/**
 
 * This is the example of value to pointer assignment. Please check rule `test12rule`.
 * Run using:
 *
 * certoraRun /home/asad/certora/tutorials-code/memorytests/test12.sol --verify test12:/home/asad/certora/tutorials-code/memorytests/test12spec.spec
 *
 * There should be no errors.
 */
 
 /**Test configurations: 
 *  Test behavior: 3D memory array double Aliasing followed by assignment 
 *  #Dimensions (D) : 3D
 *   Size       (n) : 10 > n >0
 *   Single Aliasing: No
 *   Double Aliasing: Yes
 *            Result: Killed
 *        path count: Low
 *      nonlinearity: Low
 * memory complexity: High
 *   loop complexity: High
 */

methods
{
    // When a function is not using the environment (e.g., `msg.sender`), it can be
    // declared as `envfree`
    function t12(uint8[10][10][10], uint8, uint8, uint8, uint8, uint8, uint8, uint8, uint8[10][10][10], uint8[10][10][10]) 
             external 
             returns (uint8[10][10][10] memory) 
             envfree; 
 
  }

/// @title Assignment must change the data at specified index in destination array 
rule test12rule() {


    uint8[10][10][10] dest_array3;
    uint8[10][10][10] ret3;
    uint8[10][10][10] t_array3;
    uint8[10][10][10] source_array3;

    uint8 i3;
    uint8 j3;
    uint8 k3;
    uint8 l3;
    uint8 m3;
    uint8 n3;
    uint8 value3;

    ret3 = t12(dest_array3, i3, j3, k3, l3, m3, n3, value3, source_array3, t_array3);
    require i3 < 10;
    require j3 < 10;
    require k3 < 10;
    require l3 < 10;
    require m3 < 10;
    require n3 < 10;

   
/**@title return array contains the content of the destination array
* 
*/
// Return/destination array contains values assigned to destination array at specified index
    assert ret3 [i3][k3][n3] == value3;
}