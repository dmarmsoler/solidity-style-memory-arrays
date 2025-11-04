/**
 *
 * This is the example of value to pointer assignment. Please check rule `t01rule`.
 * Run using:
 *
 * certoraRun /home/asad/certora/tutorials-code/memorytests/test01.sol --verify test01:/home/asad/certora/tutorials-code/memorytests/test01spec.spec
 *
 * There should be no errors.
 */
 
 /**Test configurations: 
 *  Test behavior: value to memory assignment
 *  #Dimensions (D) : 1D
 *   Size       (n) : n = 5
 *   Single Aliasing: No 
 *   Double Aliasing: No
 *            Result: Pass
 */
 
methods
{
    // When a function is not using the environment (e.g., `msg.sender`), it can be
    // declared as `envfree`
    function t01(uint8[5], uint8, uint8) external returns (uint8[5] memory) envfree;
  }


/// @title Assignment must change the data at specified index in destination array with value
rule t01rule() {


    uint8[5] dest_array;
    uint8[5] ret;
    
    uint8 value;
    uint8 i;
    uint8 j;

    ret = t01(dest_array, i, value);
    require i < 5;
    require i != j;
    require j < 5;
   
/**@title return array contains the content of the source array
* 
*/
    assert ret[i] == value;

/**@title return array contains the content of the destination array
* 
*/
assert ret[j] == dest_array[j];

}
