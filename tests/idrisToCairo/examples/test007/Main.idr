module Main

import Cairo

public export
%foreign 
  """
  code:
  func $name$(x) -> (result):
      tempvar a
      tempvar b
      %{
          ids.a = program_input['a']
          ids.b = program_input['b']
      %}
      if x == a * b:
        return (1)
      else:
        return (0)
      end
  end
  """
knowsSecretFactors : Felt -> Felt

%noinline
main : Cairo ()
main = output $ knowsSecretFactors 10967535067
