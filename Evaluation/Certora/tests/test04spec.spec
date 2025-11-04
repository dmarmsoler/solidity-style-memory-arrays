
/**
 * # v2p Example
 *
 * This is the example of value to pointer assignment. Please check rule `test21rule`.
 * Run using:
 *
 * certoraRun /home/asad/certora/tutorials-code/memorytests/test21.sol --verify test21:/home/asad/certora/tutorials-code/memorytests/test21spec.spec
 *
 * There should be no errors.
 */
 
 
 /**Test configurations: 
 *  Test behavior: 2D memory array single Aliasing followed by assignment 
 *  #Dimensions (D) : 2D
 *   Size       (n) : n = 20
 *   Single Aliasing: No
 *   Double Aliasing: No
 *            Result: 
 */
methods
{
    // When a function is not using the environment (e.g., `msg.sender`), it can be
    // declared as `envfree`
    function t21(uint8[20][20], uint8, uint8, uint8) external returns (uint8[20][20] memory) envfree;
  }

/// @title Assignment must change the data at specified index in destination array 
rule test21rule() {


    uint8[20][20] dest_array3;
    uint8[20][20] ret3;
    
    uint8 i3;
    uint8 j3;
    uint8 value3;

    ret3 = t21(dest_array3, i3, j3, value3);
    require i3 < 20;
    require j3 < 20;

   
/**@title return array contains the content of the source array
* 
*/
// Return/dest array contains values assigned to source array at specified index
    assert ret3 [i3][j3] == value3;
}