pragma experimental ABIEncoderV2;
contract test17 {

  
/// @notice precondition i < x.length
/// @notice precondition j <  x.length

///@notice postcondition x[i][j] == value
 function t17(uint8[][] memory x, uint8 i, uint8 j, uint8 k, uint8 value, uint8[][] memory y) 
    pure 
    public 
    returns (uint8[][] memory)  
    {
     x[i] = y[j];
      y[j][k] = value;
      return x;
    }

}
