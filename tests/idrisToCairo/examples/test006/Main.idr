module Main

import Cairo

public export
%foreign 
  """
  code:
  func Main_cheapSqrt(x) -> (result):
      tempvar result
      %{
         import math
         ids.result = int(math.sqrt(ids.x))
      %}
      assert x = result * result
      return (result)
  end
  """
cheapSqrt : Felt -> Felt

%noinline
main : Cairo ()
main = output $ cheapSqrt 25

