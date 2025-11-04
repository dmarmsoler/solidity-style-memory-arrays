pragma experimental ABIEncoderV2;
  
/// @notice precondition i < x.length
/// @notice precondition j <  x.length

///@notice postcondition x[i][j] == value
contract test25 {

  function t25(uint8[][] memory x, uint8 i, uint8 j, uint8 value) 
    pure
    public 
    returns (uint8[][] memory)  
    {
        x[i][j] = value;
      return x;
    }

}