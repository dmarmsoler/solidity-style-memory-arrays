/**
 * 
 *
 * This is the example of value to pointer assignment for a 4D memory array with n=5. Please check rule `test08rule`.
 * Run using:
 *
 * certoraRun /home/asad/certora/tutorials-code/memorytests/test08.sol --verify test08:/home/asad/certora/tutorials-code/memorytests/test08spec.spec 
 *
 * There should be no errors.
 */
 

 /**Test configurations: 
 *  Test behavior: 4D memory array single Aliasing followed by assignment 
 *  #Dimensions (D) : 3D
 *   Size       (n) : 5 > n >0
 *   Single Aliasing: Yes
 *   Double Aliasing: No
 *            Result: Killed
 *        path count: Low
 *      nonlinearity: Low
 * memory complexity: High
 *   loop complexity: High
 *
 */

methods
{
    // When a function is not using the environment (e.g., `msg.sender`), it can be
    // declared as `envfree`
    function t08(uint8[5][5][5][5], uint8, uint8, uint8, uint8, uint8, uint8, uint8 [5][5][5][5]) external returns (uint8[5][5][5][5] memory) envfree; 
 }

/// @title Assignment must change the data at specified index in destination array 
rule test08rule() {


    uint8[5][5][5][5] dest_array5;
    uint8[5][5][5][5] source_array5;
    uint8[5][5][5][5] ret5;
    
    uint8 i5;
    uint8 j5;
    uint8 k5;
    uint8 l5;
    uint8 m5;

    uint8 i50;
    uint8 j50;
    uint8 k50;
    uint8 l50;
    uint8 m50;

    uint8 value5;

    ret5 = t08(dest_array5, i5, j5, k5, l5, m5, value5, source_array5);
    
    require i5 < 5;
    require j5 < 5;    
    require k5 < 5;
    require l5 < 5;
    require m5 < 5;

   // require i50 < 5;
   // require j50 < 5;    
   // require k50 < 5;
   // require l50 < 5;
   // require m50 < 5;

    
    //require i5 != i50;
    //require j5 != j50;
    //require k5 != k50;
    //require m5 != m50;

/**@title return destination array contains the copied content of the source array at specified indeces
* 
*/
    assert ret5 [i5][k5][l5][m5] == value5;

/**@title return destination array content is preserved except the one copied to destination array
* 
*/
   // assert ret5 [i50][j50][k50][l50] == dest_array5 [i50][j50][k50][l50];
}