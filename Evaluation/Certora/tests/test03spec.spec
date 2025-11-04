/**
 * # v2p Example
 *
 * This is the example of value to pointer assignment. Please check rule `test02rule`.
 * Run using:
 *
 * certoraRun /home/asad/certora/tutorials-code/memorytests/test02.sol --verify test02:/home/asad/certora/tutorials-code/memorytests/test02spec.spec
 *
 * There should be no errors.
 */
 
  
 /**Test configurations: 
 *  Test behavior: value to memory assignment
 *  #Dimensions (D) : 1D
 *   Size       (n) : n = 20
 *   Single Aliasing: No 
 *   Double Aliasing: No
 *            Result: Pass
 */
methods
{
    // When a function is not using the environment (e.g., `msg.sender`), it can be
    // declared as `envfree`
    function t02(uint8[20], uint8, uint8) external returns (uint8[20] memory) envfree;
}


/// @title Assignment must change the data at specified index in destination array with value
rule test02rule() {


    uint8[20] dest_array;
    uint8[20] ret;
    
    uint8 value;
    uint8 i;
    uint8 j;

    ret = t02(dest_array, i, value);
    require i < 20;
    require i != j;
    require j < 20;
   
/**@title return array contains the content of the source array
* 
*/
    assert ret[i] == value;

/**@title return array contains the content of the destination array
* 
*/
    assert ret[j] == dest_array[j];

}
