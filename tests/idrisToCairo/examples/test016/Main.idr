module Main
import Cairo

import Data.Maybe

data Treemap = Empty | Branch Felt Felt Treemap Treemap

put : Felt -> Felt -> Treemap -> Treemap
put key value Empty = Branch key value Empty Empty
put key value (Branch key' value' left right) =
  if key == key'
    then Branch key value left right
    else if key `is_le_felt` key'
      then Branch key' value' (put key value left) right
      else Branch key' value' left (put key value right)

get : Felt -> Treemap -> Maybe Felt
get _ Empty = Nothing
get key (Branch key' value' left right) = 
  if key == key'
    then Just value'
    else if key `is_le_felt` key'
      then get key left
      else get key right

getOrDefault : Felt -> Felt -> Treemap -> Felt
getOrDefault key def map =
  case get key map of
    Nothing => def
    Just res => res

outputTreemap : Treemap -> Cairo ()
outputTreemap Empty = pure ()
outputTreemap (Branch key value left right) = do
  outputTreemap left
  output key
  output value
  outputTreemap right

exampleMap : Treemap
exampleMap = let m1 = put 1 11 Empty
                 m2 = put 2 22 m1
                 m3 = put 3 33 m2
                 m4 = put 4 44 m3
              in m4

%noinline
main : Cairo ()
main = do
  outputTreemap exampleMap
  output $ getOrDefault 2 (-1) exampleMap
  output $ getOrDefault 3 (-1) exampleMap
  output $ getOrDefault 5 (-1) exampleMap

