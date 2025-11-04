
contract test02 {
  
/// @notice precondition i < 20
/// @notice precondition i < x.length
/// @notice postcondition x[i] == y

    function t02(uint8[20] memory x, uint8 i, uint8 y) 
    public 
    returns (uint8[20] memory)  
    {
      x[i] = y;
      return x;
    }
}