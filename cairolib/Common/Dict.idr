module Common.Dict

import Common

-- module Data.Linear.Array
-- https://arxiv.org/pdf/1710.09756.pdf


-- How to implement LinDict Felt SomeOtherType? 
-- And store the Felt as the address to the value? 

record Dict where
  constructor MkDict 
  dict_ptr: Felt

export
data LinDict : Type where
  MkLinDict : (1 _:Dict) -> LinDict

%foreign 
    "imports:starkware.cairo.common.default_dict default_dict_new"
    "untupled:(_,_)"
    """
    code:
    func Common_Dict_dnew(default_value, world) -> (world, dict):
        let (dict_ptr) = default_dict_new(default_value)
        return (world, cast(dict_ptr, felt))
    end
    """
dnew :  Felt -> PrimCairo Felt

export
%foreign 
    "imports:starkware.cairo.common.dict_access DictAccess, starkware.cairo.common.dict dict_read"
    "untupled:(_,_)"
    """
    code:
    func Common_Dict_dread(dict, key) -> (dict, value):
       let dict_end_ptr = cast(dict, DictAccess*)
       let (res) = dict_read{dict_ptr=dict_end_ptr}(key)
       return (cast(dict_end_ptr, felt), res)
    end
    """
dread : (1 d: LinDict) -> (key : Felt) -> (LinDict, Felt) -- The key must be present. Better would be Maybe Felt

export
%foreign 
    "imports:starkware.cairo.common.dict_access DictAccess, starkware.cairo.common.dict dict_write"
    """
    code:
    func Common_Dict_dwrite(dict, key, value) -> (dict_ptr):
       let dict_end_ptr = cast(dict, DictAccess*)
       dict_write{dict_ptr=dict_end_ptr}(key, value)
       return (cast(dict_end_ptr, felt))
    end
    """
dwrite : (1 d: LinDict) -> (key : Felt) -> (value : Felt) -> LinDict

%foreign 
    "imports:starkware.cairo.common.dict_access DictAccess, starkware.cairo.common.default_dict default_dict_finalize"
    "linear_implicits:range_check_ptr"
    """
    code:
    func Common_Dict_dverify(range_check_ptr, def_value, dict_start, dict_end, world) -> (world,range_check_ptr):
        let (squashed_dict_start, squashed_dict_end) = default_dict_finalize{range_check_ptr=range_check_ptr}(
             cast(dict_start, DictAccess*), cast(dict_end,DictAccess*), def_value)
       return (world, range_check_ptr)
    end
    """
    -- Should we return the squashed dict?
    -- Should we offer Verified Dict and Unverified dict? A write would lead to a linear Unverified dict.
dverify : (def_value:Felt) -> (dict_start:Felt) -> (1 _: LinDict) -> PrimCairoUnit 

-- Creates a new dict which is then passed to the continutation k
-- At the end the dict is verified
public export %inline
dict : Felt -> (1 k : (1 d : LinDict ) -> (LinDict, a)) -> Cairo a
dict def k  = fromPrimCairo $ \(out_ptr) => 
       let MkCairoRes out_ptr' dict_start = dnew def out_ptr
           (dict_end, a) = k (MkLinDict $ MkDict dict_start)
           out_ptr'' = dverify def dict_start dict_end out_ptr'
        in MkCairoRes out_ptr'' a 
