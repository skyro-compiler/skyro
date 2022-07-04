# Implements a simple, immutable tree map.

from starkware.cairo.common.alloc import alloc
from starkware.cairo.common.registers import get_fp_and_pc
from starkware.cairo.common.serialize import serialize_word
from starkware.cairo.common.math import assert_lt_felt
from starkware.cairo.common.math_cmp import is_le_felt

struct TreeMap:
    member key: felt
    member value: felt
    member left: TreeMap*
    member right: TreeMap*
    member empty: felt # 0 non_empty, 1 empty
end


struct Result:
    member value: felt
    member empty: felt # 0 found value, 1 key not found
end

const false = 0
const true = 1

# Creates an empty map
func empty() -> (map: TreeMap*):
    alloc_locals
    local empty_map: TreeMap
    #assert empty_map.key = 0
    #assert empty_map.value = 0
    #assert empty_map.left = 0
    #assert empty_map.right = 0
    assert empty_map.empty = true
    let (__fp__, _) = get_fp_and_pc()
    return (&empty_map)
end

# Returns a new map containing the given key->value entry
func put{range_check_ptr}(key, value, map: TreeMap*) -> (map: TreeMap*):
    alloc_locals
    local result: TreeMap

    if map.empty == true:
        assert result.key = key
        assert result.value = value
        assert result.left = map # the empty map
        assert result.right = map # the empty map
        assert result.empty = false
        let (__fp__, _) = get_fp_and_pc()
        return (&result)
    else:
        if key == map.key:
            assert result.key = map.key
            assert result.value = value
            assert result.left = map.left
            assert result.right = map.right
            assert result.empty = false
            let (__fp__, _) = get_fp_and_pc()
            return (&result)
        else: 
            let (local go_left) = is_le_felt(key, map.key)
            if go_left == true:

                let (new_left) = put(key,value, map.left)
                assert result.key = map.key
                assert result.value = map.value
                assert result.left = new_left
                assert result.right = map.right
                assert result.empty = false
                let (__fp__, _) = get_fp_and_pc()
                return (&result)
            else:

                let (new_right) = put(key,value, map.right)
                assert result.key = map.key
                assert result.value = map.value
                assert result.left = map.left
                assert result.right = new_right
                assert result.empty = false
                let (__fp__, _) = get_fp_and_pc()
                return (&result)
            end
        end
    end
end

# Returns a Result containing the value for the given key.
# If the key can not be found in the map the result is marked with empty = 1.
func get{range_check_ptr}(key, map: TreeMap*) -> (result: Result*):
    alloc_locals
    local result: Result
    if map.empty == true:
        # assert result.value = 0
        assert result.empty = true
        let (__fp__, _) = get_fp_and_pc()
        return (&result)
    else:
        if key == map.key:
            assert result.value = map.value
            assert result.empty = false
            let (__fp__, _) = get_fp_and_pc()
            return (&result)
        else: 
            let (local go_left) = is_le_felt(key, map.key)
            if go_left == true:
                return get(key, map.left)
            else:
                return get(key, map.right)
            end
        end
    end
end


# Returns the given default value if no entry can be found in the given map.
func get_or_default{range_check_ptr}(key, defaulValue, map: TreeMap*) -> (value: felt):
    let (result) = get(key, map)
    if result.empty == true:
        return (defaulValue)
    else:
        return (result.value)
    end
end


# Preorder output of the map.
func output_treemap{output_ptr: felt*}(map: TreeMap*):
    if map.empty == true:
        return ()
    else:
        output_treemap(map.left)

        serialize_word(map.key)
        serialize_word(map.value)

        output_treemap(map.right)
        return ()
    end
end


