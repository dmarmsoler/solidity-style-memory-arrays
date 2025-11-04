/**
 * # dynamicv2p Example
 *
 * This is the example of value to pointer assignment for a single dimenstional dynamic array. Please check rule `test13rule`.
 * Run using:
 *
 * certoraRun /home/asad/certora/tutorials-code/memorytests/test13.sol --verify test13:/home/asad/certora/tutorials-code/memorytests/test13spec.spec
 *
 * There should be no errors.
 */
 
 /**Test configurations: 
 *  Test behavior: vlaue assignment to a dynamic 1D memory array  
 *  #Dimensions (D) : 1D
 *   Size       (n) : NA
 *   Single Aliasing: No
 *   Double Aliasing: No
 * Dynamic (n bound): Yes (200 > n > 0)
 *         loop_iter: 200
 *            Result: Pass
 */

methods
{
    // When a function is not using the environment (e.g., `msg.sender`), it can be
    // declared as `envfree`
    function t13(uint8[], uint8, uint8) external returns (uint8[] memory) envfree;
}


/// @title Assignment must change the data at specified index in destination array with value
rule test13rule() {


    uint8[] dest_array;
    uint8[] ret;
    
    uint8 value;
    uint8 i;
   // uint8 j;
    
// Ensure array has at least one element
    require dest_array.length > 0;
    // Limit size to avoid loop unwinding issues
    require dest_array.length < 200;
    // Ensure i is a valid index (strictly less than length)
    require i < dest_array.length;

    
    ret = t13(dest_array, i, value);

    // Check the assigned value
    assert ret[i] == value;
}

