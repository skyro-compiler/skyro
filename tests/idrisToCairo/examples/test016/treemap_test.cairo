%builtins output range_check

from starkware.cairo.common.serialize import serialize_word

from treemap import TreeMap
from treemap import Result
from treemap import empty
from treemap import put
from treemap import get
from treemap import get_or_default
from treemap import output_treemap

# "Tests" insert and lookup
func main{output_ptr : felt*, range_check_ptr}() -> ():
    alloc_locals
    let (map) = empty()
    let (map) = put(2, 22, map) # 2->22
    let (map) = put(3, 32, map) # 2->22, 3->32
    let (map) = put(4, 44, map) # 2->22, 3->32, 4->44
    let (map) = put(3, 33, map) # 2->22, 3->33, 4->44
    let (local map: TreeMap*) = put(1, 11, map) # 1->11, 2->22, 3->33, 4->44

    output_treemap(map)

    let (res) = get_or_default(2, -1, map) 
    serialize_word(res)

    let (res) = get_or_default(3, -1, map)
    serialize_word(res)

    let (res) = get_or_default(5, -1, map)
    serialize_word(res)

    return ()
end

#> cairo-compile treemap_test.cairo --output treemap_test_compiled.json && cairo-run --program=treemap_test_compiled.json --print_output --layout=small
