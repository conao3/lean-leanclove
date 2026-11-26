import Std

namespace LeanClove

def first (xs : List α) : Option α := xs.head?
def rest (xs : List α) : List α := xs.tail

def next (xs : List α) : Option (List α) :=
  match rest xs with
  | [] => none
  | y :: ys => Option.some (y :: ys)

def cons (x : α) (xs : List α) : List α := x :: xs
def conj (xs : List α) (x : α) : List α := cons x xs
def concat (xs ys : List α) : List α := xs ++ ys
def last (xs : List α) : Option α := xs.getLast?
def butlast (xs : List α) : List α := xs.dropLast
def nth (xs : List α) (i : Nat) : Option α := xs[i]?

@[simp] theorem first_cons (x : α) (xs : List α) : first (cons x xs) = Option.some x := rfl
@[simp] theorem rest_cons (x : α) (xs : List α) : rest (cons x xs) = xs := rfl
@[simp] theorem first_conj (xs : List α) (x : α) : first (conj xs x) = Option.some x := rfl

theorem next_eq_none_iff (xs : List α) : next xs = none ↔ xs.length ≤ 1 := by
  rcases xs with _ | ⟨x, _ | ⟨y, ys⟩⟩ <;> simp [next, rest]

theorem concat_assoc (xs ys zs : List α) :
    concat (concat xs ys) zs = concat xs (concat ys zs) :=
  List.append_assoc xs ys zs

theorem last_concat (xs ys : List α) : last (concat xs ys) = (last ys).or (last xs) :=
  List.getLast?_append

@[simp] theorem length_butlast (xs : List α) : (butlast xs).length = xs.length - 1 :=
  List.length_dropLast

theorem nth_eq_none_iff (xs : List α) (i : Nat) : nth xs i = none ↔ xs.length ≤ i :=
  List.getElem?_eq_none_iff

def take (n : Nat) (xs : List α) : List α := xs.take n
def drop (n : Nat) (xs : List α) : List α := xs.drop n
def takeWhile (p : α → Bool) (xs : List α) : List α := xs.takeWhile p
def dropWhile (p : α → Bool) (xs : List α) : List α := xs.dropWhile p

@[simp] theorem take_append_drop (n : Nat) (xs : List α) : take n xs ++ drop n xs = xs :=
  List.take_append_drop n xs

@[simp] theorem takeWhile_append_dropWhile (p : α → Bool) (xs : List α) :
    takeWhile p xs ++ dropWhile p xs = xs :=
  List.takeWhile_append_dropWhile

@[simp] theorem length_take (n : Nat) (xs : List α) :
    (take n xs).length = min n xs.length := List.length_take

@[simp] theorem length_drop (n : Nat) (xs : List α) :
    (drop n xs).length = xs.length - n := List.length_drop

/-- Non-overlapping chunks, including a short final chunk. A size of zero gives no chunks. -/
def partitionAll (n : Nat) (xs : List α) : List (List α) :=
  match n, xs with
  | 0, _ | _, [] => []
  | n + 1, x :: xs => take (n + 1) (x :: xs) :: partitionAll (n + 1) (drop (n + 1) (x :: xs))
termination_by xs.length
decreasing_by simp [drop]; omega

/-- Non-overlapping full chunks; discard a short final chunk. -/
def partition (n : Nat) (xs : List α) : List (List α) :=
  (partitionAll n xs).filter fun ys => ys.length == n

theorem flatten_partitionAll (n : Nat) (xs : List α) (hn : 0 < n) :
    (partitionAll n xs).flatten = xs := by
  match n, xs with
  | n + 1, [] => simp [partitionAll]
  | n + 1, x :: xs =>
    rw [partitionAll, List.flatten_cons, flatten_partitionAll (n + 1) (drop (n + 1) (x :: xs)) hn,
      take_append_drop]
termination_by xs.length
decreasing_by simp [drop]; omega

theorem length_of_mem_partition {n : Nat} {xs ys : List α} (h : ys ∈ partition n xs) :
    ys.length = n := by
  exact beq_iff_eq.mp (List.mem_filter.mp h).2

def interleave : List α → List α → List α
  | x :: xs, y :: ys => x :: y :: interleave xs ys
  | _, _ => []

@[simp] theorem length_interleave (xs ys : List α) :
    (interleave xs ys).length = 2 * min xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [interleave]
  | cons x xs ih =>
    cases ys with
    | nil => simp [interleave]
    | cons y ys => simp [interleave, ih]; omega

def interpose (sep : α) (xs : List α) : List α := xs.intersperse sep

@[simp] theorem length_interpose (sep : α) (xs : List α) :
    (interpose sep xs).length = 2 * xs.length - 1 :=
  List.length_intersperse

def distinct [BEq α] (xs : List α) : List α := xs.eraseDups

@[simp] theorem mem_distinct [BEq α] [LawfulBEq α] {x : α} {xs : List α} :
    x ∈ distinct xs ↔ x ∈ xs := List.mem_eraseDups

theorem nodup_distinct [BEq α] [LawfulBEq α] (xs : List α) : (distinct xs).Nodup := by
  match xs with
  | [] => simp [distinct]
  | x :: xs =>
    change (x :: xs).eraseDups.Nodup
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨?_, nodup_distinct (xs.filter fun y => !(y == x))⟩
    intro h
    have hm : x ∈ distinct (xs.filter fun y => !(y == x)) := h
    simpa using (List.mem_filter.mp (mem_distinct.mp hm)).2
termination_by xs.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private def dedupeAfter [BEq α] (prev : α) : List α → List α
  | [] => []
  | x :: xs => if prev == x then dedupeAfter prev xs else x :: dedupeAfter x xs

/-- Retain only the first element of each run of equal values. -/
def dedupe [BEq α] : List α → List α
  | [] => []
  | x :: xs => x :: dedupeAfter x xs

private theorem dedupeAfter_sublist [BEq α] (prev : α) (xs : List α) :
    List.Sublist (dedupeAfter prev xs) xs := by
  induction xs generalizing prev with
  | nil => exact .slnil
  | cons x xs ih =>
    by_cases h : (prev == x) = true
    · simpa [dedupeAfter, h] using (ih prev).cons x
    · simpa [dedupeAfter, h] using (ih x).cons_cons x

theorem dedupe_sublist [BEq α] (xs : List α) : List.Sublist (dedupe xs) xs := by
  cases xs with
  | nil => exact .slnil
  | cons x xs => exact (dedupeAfter_sublist x xs).cons_cons x

theorem dedupe_cons_self [BEq α] [LawfulBEq α] (x : α) (xs : List α) :
    dedupe (x :: x :: xs) = dedupe (x :: xs) := by simp [dedupe, dedupeAfter]

def mapcat (f : α → List β) (xs : List α) : List β := xs.flatMap f
def keep (f : α → Option β) (xs : List α) : List β := xs.filterMap f
def mapIndexed (f : Nat → α → β) (xs : List α) : List β := xs.mapIdx f
def keepIndexed (f : Nat → α → Option β) (xs : List α) : List β :=
  keep id (mapIndexed f xs)

theorem mapcat_append (f : α → List β) (xs ys : List α) :
    mapcat f (xs ++ ys) = mapcat f xs ++ mapcat f ys := List.flatMap_append

theorem keep_append (f : α → Option β) (xs ys : List α) :
    keep f (xs ++ ys) = keep f xs ++ keep f ys := List.filterMap_append

@[simp] theorem length_mapIndexed (f : Nat → α → β) (xs : List α) :
    (mapIndexed f xs).length = xs.length := List.length_mapIdx

theorem length_keepIndexed_le (f : Nat → α → Option β) (xs : List α) :
    (keepIndexed f xs).length ≤ xs.length := by
  simpa [keepIndexed, keep, mapIndexed] using List.length_filterMap_le id (xs.mapIdx f)

def reductions (f : β → α → β) (init : β) (xs : List α) : List β := xs.scanl f init

@[simp] theorem length_reductions (f : β → α → β) (init : β) (xs : List α) :
    (reductions f init xs).length = xs.length + 1 := List.length_scanl

@[simp] theorem last_reductions (f : β → α → β) (init : β) (xs : List α) :
    last (reductions f init xs) = Option.some (xs.foldl f init) := List.getLast?_scanl

/-- The first `n` terms of repeated application, starting with the seed. -/
def iterate : Nat → (α → α) → α → List α
  | 0, _, _ => []
  | n + 1, f, seed => seed :: iterate n f (f seed)

def «repeat» (n : Nat) (x : α) : List α := List.replicate n x
def range (n : Nat) : List Nat := List.range n

@[simp] theorem length_iterate (n : Nat) (f : α → α) (seed : α) :
    (iterate n f seed).length = n := by
  induction n generalizing seed with
  | zero => rfl
  | succ n ih => simp [iterate, ih]

@[simp] theorem length_repeat (n : Nat) (x : α) : (LeanClove.«repeat» n x).length = n :=
  List.length_replicate

@[simp] theorem length_range (n : Nat) : (range n).length = n := List.length_range

/-- Return the first result accepted by an Option-valued callback. -/
def some (f : α → Option β) (xs : List α) : Option β := xs.findSome? f
def every? (p : α → Bool) (xs : List α) : Bool := xs.all p
def notAny? (p : α → Bool) (xs : List α) : Bool := !(xs.any p)

theorem some_eq_none_iff (f : α → Option β) (xs : List α) :
    some f xs = none ↔ ∀ x ∈ xs, f x = none := List.findSome?_eq_none_iff

theorem every_eq_true_iff (p : α → Bool) (xs : List α) :
    every? p xs = true ↔ ∀ x ∈ xs, p x = true := List.all_eq_true

theorem notAny_eq_true_iff (p : α → Bool) (xs : List α) :
    notAny? p xs = true ↔ ∀ x ∈ xs, p x = false := by simp [notAny?, List.any_eq_false]

end LeanClove
