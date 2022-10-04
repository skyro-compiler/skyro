module Cairo.Output

import Common

public export
%foreign 
    "apStable:True"
    """
    code:
    func $name$(value, output_ptr) -> (output_ptr):
        assert [output_ptr] = value
        return (output_ptr + 1)
    end
    """
cairooutput : Felt -> PrimCairoUnit

-- Outputs the given value (and keeps track ouf the output_ptr)
public export %inline
output : Felt -> Cairo ()
output val = fromPrimCairoUnit (cairooutput val)
