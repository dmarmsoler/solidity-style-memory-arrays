/**
 * This is the example of value to pointer assignment for a single dimenstional dynamic array. Please check rule `test14rule`.
 * Run using:
 *
 * certoraRun /home/asad/certora/tutorials-code/memorytests/test14.sol --verify test14:/home/asad/certora/tutorials-code/memorytests/test14spec.spec
 *
 * There should be no errors.
 */
 
 /**Test configurations: 
 *  Test behavior: Single aliasing with 2D dynamic memory array  
 *  #Dimensions (D) : 2D
 *   Size       (n) : NA
 *   Single Aliasing: Yes
 *   Double Aliasing: No
 * Dynamic (n bound): Yes (5 > n > 0)
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
 function t14(uint8[][], uint8, uint8, uint8, uint8, uint8[][]) external returns (uint8[][] memory) envfree;
}

/// @title Assignment must change the data at specified index in destination array 
rule test14rule() {


    uint8[][] dest_array;
    uint8[][] ret;
    
    uint8[][] source_array;
    uint8 i;
    uint8 j;
    uint8 k;
    uint8 l;
    uint8 m;
    uint8 n;
    uint8 value;

    require dest_array.length   > 0;
    require source_array.length > 0;
    require dest_array.length   < 5;
    require source_array.length < 5;
    require i < dest_array.length;
    require j < dest_array.length;
    require k < source_array.length;
    require l < source_array.length;

    ret = t14(dest_array,i, j, k, value, source_array);

 
/**@title return array contains the content of the source array
* 
*/
    assert ret[i][k] == value;
    //assert ret[l][m] == dest_array[l][m];
    //assert ret[i][n] == source_array[j][n];
}