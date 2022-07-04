module Main
import Cairo

%noinline
main : Cairo ()
main = do
  builder <- createSegmentBuilder
  let segment1 = freeze (append 3 (append 2 (append 1 builder)))
  output $ index 1 segment1

  let segment2 = listToSegment [4,5,6,7]
  output $ index 0 segment2
  output $ index 3 segment2
  output $ size segment2

  _ <- traverse output (segmentToList segment2)

  output $ unsafeHead segment2
  output $ unsafeHead (unsafeTail segment2)
  output $ size (unsafeTail segment2)
  pure ()

  

