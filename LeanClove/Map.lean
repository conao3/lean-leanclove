import Std.Data.HashMap

namespace LeanClove

open Std (HashMap)

section
variable {κ α : Type _} [BEq κ] [Hashable κ]

def get (m : HashMap κ α) (key : κ) : Option α := m[key]?
def assoc (m : HashMap κ α) (key : κ) (value : α) : HashMap κ α := m.insert key value
def dissoc (m : HashMap κ α) (key : κ) : HashMap κ α := m.erase key

/-- Pass the old value (or `none`) to the callback and insert its result. -/
def update (m : HashMap κ α) (key : κ) (f : Option α → α) : HashMap κ α :=
  assoc m key (f (get m key))

/-- Combine two maps, preferring the right map on collisions. -/
def merge (left right : HashMap κ α) : HashMap κ α := left ∪ right

def selectKeys (m : HashMap κ α) (keys : List κ) : HashMap κ α :=
  m.filter fun key _ => keys.contains key

def zipmap (keys : List κ) (values : List α) : HashMap κ α :=
  HashMap.ofList (keys.zip values)

theorem get_assoc [LawfulBEq κ] (m : HashMap κ α) (key query : κ) (value : α) :
    get (assoc m key value) query = if key == query then Option.some value else get m query :=
  HashMap.getElem?_insert

theorem get_dissoc [LawfulBEq κ] (m : HashMap κ α) (key query : κ) :
    get (dissoc m key) query = if key == query then none else get m query :=
  HashMap.getElem?_erase

@[simp] theorem get_update [LawfulBEq κ] (m : HashMap κ α) (key : κ) (f : Option α → α) :
    get (update m key f) key = Option.some (f (get m key)) :=
  HashMap.getElem?_insert_self

theorem get_merge [LawfulBEq κ] (left right : HashMap κ α) (key : κ) :
    get (merge left right) key = (get right key).or (get left key) :=
  HashMap.getElem?_union

theorem get_selectKeys [LawfulBEq κ] (m : HashMap κ α) (keys : List κ) (key : κ) :
    get (selectKeys m keys) key = if keys.contains key then get m key else none := by
  unfold get selectKeys
  rw [HashMap.getElem?_filter']
  cases keys.contains key <;> cases m[key]? <;> rfl

theorem get_zipmap_of_mem [LawfulBEq κ] {keys : List κ} {values : List α}
    {key : κ} {value : α}
    (distinctKeys : (keys.zip values).Pairwise fun a b => (a.1 == b.1) = false)
    (h : (key, value) ∈ keys.zip values) :
    get (zipmap keys values) key = Option.some value :=
  HashMap.getElem?_ofList_of_mem (beq_self_eq_true _) distinctKeys h

/-- Group values without changing their relative order within a group. -/
def groupBy (f : α → κ) (xs : List α) : HashMap κ (List α) :=
  xs.foldr (fun x m => update m (f x) fun group => x :: group.getD []) ∅

theorem getD_groupBy [LawfulBEq κ] (f : α → κ) (xs : List α) (key : κ) :
    (get (groupBy f xs) key).getD [] = xs.filter fun x => f x == key := by
  induction xs with
  | nil => simp [groupBy, get]
  | cons x xs ih =>
    change (get (update (groupBy f xs) (f x) fun group => x :: group.getD []) key).getD [] = _
    rw [update, get_assoc, List.filter_cons]
    by_cases h : (f x == key) = true
    · have he := beq_iff_eq.mp h
      simp [he, ih]
    · simp [h, ih]

end

section
variable {α : Type _} [BEq α] [Hashable α]

private def bump (m : HashMap α Nat) (x : α) : HashMap α Nat :=
  update m x fun old => old.getD 0 + 1

def frequencies (xs : List α) : HashMap α Nat := xs.foldl bump ∅

private theorem getD_foldl_bump [LawfulBEq α] (m : HashMap α Nat) (xs : List α) (key : α) :
    (get (xs.foldl bump m) key).getD 0 =
      (get m key).getD 0 + xs.countP (fun x => x == key) := by
  induction xs generalizing m with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, bump, update, get_assoc, List.countP_cons]
    by_cases h : (x == key) = true
    · have he := beq_iff_eq.mp h
      simp [he]
      omega
    · simp [h]

theorem getD_frequencies [LawfulBEq α] (xs : List α) (key : α) :
    (get (frequencies xs) key).getD 0 = xs.countP (fun x => x == key) := by
  rw [frequencies, getD_foldl_bump]
  simp [get]

private theorem filter_key_toList [LawfulBEq α] (m : HashMap α Nat) (key : α) :
    (m.toList.filter fun p => key == p.1) = (m[key]?.map fun n => (key, n)).toList := by
  have mem_filter (n : Nat) :
      (key, n) ∈ (m.toList.filter fun p => key == p.1) ↔ m[key]? = Option.some n := by simp
  have key_of_mem (p : α × Nat) (hp : p ∈ (m.toList.filter fun p => key == p.1)) : p.1 = key :=
    (beq_iff_eq.mp (List.mem_filter.mp hp).2).symm
  have distinct := (HashMap.distinct_keys_toList (m := m)).filter (fun (p : α × Nat) => key == p.1)
  generalize h : (m.toList.filter fun p => key == p.1) = ps at mem_filter key_of_mem distinct ⊢
  cases ps with
  | nil =>
    cases hv : m[key]? with
    | none => rfl
    | some n => exact False.elim (by simpa using (mem_filter n).mpr hv)
  | cons p ps =>
    obtain ⟨k, v⟩ := p
    have he : k = key := key_of_mem (k, v) (by simp)
    subst k
    have hv := (mem_filter v).mp (by simp)
    cases ps with
    | nil => simp [hv]
    | cons q qs =>
      have hq : q.1 = key := key_of_mem q (by simp)
      have hn := (List.pairwise_cons.mp distinct).1 q (by simp)
      simp [hq] at hn

private theorem sum_bump [LawfulBEq α] (m : HashMap α Nat) (key : α) :
    ((bump m key).toList.map Prod.snd).sum = (m.toList.map Prod.snd).sum + 1 := by
  have hins := (HashMap.toList_insert_perm (m := m) (k := key)
    (v := (get m key).getD 0 + 1)).map Prod.snd
  have hsplit := (List.filter_append_perm (fun (p : α × Nat) => key == p.1) m.toList).map Prod.snd
  have hi := hins.sum_nat
  have hs := hsplit.sum_nat
  change ((bump m key).toList.map Prod.snd).sum = _ at hi
  rw [List.map_append, List.sum_append_nat, filter_key_toList] at hs
  simp only [List.map_cons, List.sum_cons] at hi
  cases hv : m[key]? <;> simp [get, hv] at hi hs <;> omega

private theorem sum_foldl_bump [LawfulBEq α] (m : HashMap α Nat) (xs : List α) :
    ((xs.foldl bump m).toList.map Prod.snd).sum = (m.toList.map Prod.snd).sum + xs.length := by
  induction xs generalizing m with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, sum_bump, List.length_cons]
    omega

theorem sum_frequencies [LawfulBEq α] (xs : List α) :
    ((frequencies xs).toList.map Prod.snd).sum = xs.length := by
  rw [frequencies, sum_foldl_bump]
  simp

end

end LeanClove
