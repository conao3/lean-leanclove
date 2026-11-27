import LeanClove

namespace LeanClove.Test

#guard first ([] : List Nat) == none
#guard first (cons 1 [2, 3]) == Option.some 1
#guard rest (conj [2, 3] 1) == [2, 3]
#guard next [1] == none
#guard next [1, 2, 3] == Option.some [2, 3]
#guard concat [1, 2] [3, 4] == [1, 2, 3, 4]
#guard last [1, 2] == Option.some 2
#guard last ([] : List Nat) == none
#guard butlast [1, 2, 3] == [1, 2]
#guard butlast [1] == []
#guard nth [1, 2] 1 == Option.some 2
#guard nth [1, 2] 2 == none

#guard take 5 [1, 2] == [1, 2]
#guard drop 5 [1, 2] == []
#guard take 2 [1, 2, 3] == [1, 2]
#guard drop 2 [1, 2, 3] == [3]
#guard takeWhile (· < 3) [1, 2, 3, 1] == [1, 2]
#guard dropWhile (· < 3) [1, 2, 3, 1] == [3, 1]
#guard partitionAll 2 [1, 2, 3, 4, 5] == [[1, 2], [3, 4], [5]]
#guard partitionAll 0 [1, 2] == []
#guard partition 2 [1, 2, 3, 4, 5] == [[1, 2], [3, 4]]
#guard partition 5 [1, 2] == []
#guard interleave [1, 2, 3] [4, 5] == [1, 4, 2, 5]
#guard interpose 0 [1, 2, 3] == [1, 0, 2, 0, 3]
#guard interpose 0 [] == []

#guard distinct [3, 1, 3, 2, 1] == [3, 1, 2]
#guard dedupe [3, 3, 1, 3, 3, 2, 2] == [3, 1, 3, 2]
#guard mapcat (fun n => [n, n + 1]) [1, 3] == [1, 2, 3, 4]
#guard keep (fun n => if n == 2 then none else Option.some false) [1, 2, 3] == [false, false]
#guard mapIndexed (· + ·) [10, 20, 30] == [10, 21, 32]
#guard keepIndexed (fun i x => if x == 20 then none else Option.some i) [10, 20, 30] == [0, 2]
#guard reductions (· + ·) 10 [1, 2, 3] == [10, 11, 13, 16]
#guard reductions (· + ·) 10 ([] : List Nat) == [10]
#guard iterate 4 (· * 2) 1 == [1, 2, 4, 8]
#guard iterate 0 (· * 2) 1 == []
#guard LeanClove.repeat 3 "x" == ["x", "x", "x"]
#guard range 4 == [0, 1, 2, 3]
#guard LeanClove.some (fun n => if n > 1 then Option.some n else none) [1, 2, 3] == Option.some 2
#guard LeanClove.some (fun _ => Option.some false) [0] == Option.some false
#guard every? (· < 3) [0, 2]
#guard every? (fun _ => false) ([] : List Nat)
#guard notAny? (· > 3) [1, 2, 3]
#guard !(notAny? (· == 2) [1, 2, 3])

private def m : Std.HashMap String Nat := zipmap ["a", "b", "a", "unpaired"] [1, 2, 3]
#guard get m "a" == Option.some 3
#guard get m "unpaired" == none
#guard get (assoc m "b" 4) "b" == Option.some 4
#guard get (dissoc m "a") "a" == none
#guard get (dissoc m "a") "b" == Option.some 2
#guard get (update m "a" (fun v => v.getD 0 + 1)) "a" == Option.some 4
#guard get (update m "c" (fun v => v.getD 0 + 1)) "c" == Option.some 1
#guard get (merge m (zipmap ["a"] [7])) "a" == Option.some 7
#guard get (merge m (zipmap ["a"] [7])) "b" == Option.some 2
#guard get (selectKeys m ["a", "missing", "a"]) "a" == Option.some 3
#guard get (selectKeys m ["a"]) "b" == none
#guard get (selectKeys m ["missing"]) "missing" == none

private structure SelectionKey where
  id : Nat
  label : String

private instance : BEq SelectionKey where
  beq a b := a.id == b.id

private instance : Hashable SelectionKey where
  hash key := hash key.id

#guard
  let stored : SelectionKey := { id := 1, label := "stored" }
  let original := zipmap [stored] [42]
  let requested : SelectionKey := { id := 1, label := "requested" }
  ((selectKeys original [requested]).getKey? requested).map SelectionKey.label == Option.some "stored"

#guard get (groupBy (· % 2) [1, 3, 2, 5, 4]) 1 == Option.some [1, 3, 5]
#guard get (groupBy (· % 2) [1, 3, 2, 5, 4]) 0 == Option.some [2, 4]
#guard get (groupBy (· % 2) [1, 3]) 0 == none
#guard get (frequencies ["a", "b", "a"]) "a" == Option.some 2
#guard get (frequencies ["a", "b", "a"]) "b" == Option.some 1
#guard get (frequencies ["a", "b", "a"]) "missing" == none
#guard ((frequencies ["a", "b", "a"]).toList.map Prod.snd).sum == 3

#guard identity 7 == 7
#guard constantly "fixed" true == "fixed"
#guard comp (· * 3) (· + 1) 2 == 9
#guard LeanClove.partial Nat.sub 10 3 == 7
#guard complement (· == 1) 2
#guard fnil (· + 1) 10 none == 11
#guard fnil (· + 1) 10 (Option.some 7) == 8
#guard juxt [(· + 1), (· * 3)] 2 == [3, 6]

end LeanClove.Test
