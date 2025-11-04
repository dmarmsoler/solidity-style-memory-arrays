
/**
 * # v2p Example
 *
 * This is the example of value to pointer assignment. Please check rule `test25rule`.
 * Run using:
 *
 * certoraRun /home/asad/certora/tutorials-code/memorytests/test25.sol --verify test25:/home/asad/certora/tutorials-code/memorytests/test25spec.spec --loop_iter 25
 *
 * There should be no errors.
 */
 
 
 /**Test configurations: 
 *  Test behavior: 2D dynamic memory array value assignment 
 *  #Dimensions (D) : 2D
 *   Size       (n) : n = 5
 *   Single Aliasing: No
 *   Double Aliasing: No
 *            Result: Voilated
 *             Error: Unwinding condition in a loop. 
                    We recommend to run with `--optimistic_loop`, or increase `--loop_iter` to a value higher than 25. 
                    Please consult our documentation to be aware of the consequences on soundness when setting this flag.
 */
methods
{
    // When a function is not using the environment (e.g., `msg.sender`), it can be
    // declared as `envfree`
    function t25(uint8[][], uint8, uint8, uint8) external returns (uint8[][] memory) envfree;
  }

/// @title Assignment must change the data at specified index in destination array 
rule t25() {


    uint8[][] dest_array3;
    uint8[][] ret3;
    
    uint8 i3;
    uint8 j3;
    uint8 value3;
    
   require dest_array3.length > 0;
    //require dest_array3.length < 5;
    require i3 < dest_array3.length;
    require j3 < dest_array3[i3].length;

    ret3 = t25(dest_array3, i3, j3, value3);
   

   
/**@title return array contains the content of the source array
* 
*/
// Return/dest array contains values assigned to source array at specified index
    assert ret3 [i3][j3] == value3;
}