-- Prompt: "Define a basic linked-list of some type α, and a dependent-type
-- SortedList that provides the proof the list is actually sorted with respect to the ordering on α."

namespace SortList

/-- A basic singly-linked list, generic over a type `α`. -/
inductive List (α : Type) where
  | nil : List α
  | cons : α → List α → List α
deriving Repr

/--
A proof that a `List` is sorted with respect to the `≤` ordering on `α`.

- `nil`: the empty list is sorted.
- `singleton`: a one-element list is sorted.
- `cons x y xs (hxy : x ≤ y) (h : Sorted (.cons y xs))`: prepending `x`
  is sorted if `x ≤ y` and the tail `y :: xs` is itself sorted.
-/
inductive Sorted [LE α] : List α → Prop where
  | nil : Sorted .nil
  | singleton (x : α) : Sorted (.cons x .nil)
  | cons (x y : α) (xs : List α) (hxy : x ≤ y) (h : Sorted (.cons y xs)) :
      Sorted (.cons x (.cons y xs))

/-- A sorted list: a `List` bundled with a proof that it is sorted. -/
structure SortedList (α : Type) [LE α] where
  list : List α
  sorted : Sorted list

/-- Decide at runtime whether a `List` is sorted. -/
def List.isSorted [LE α] [DecidableRel (α := α) (· ≤ ·)] : List α → Bool
  | .nil => true
  | .cons _ .nil => true
  | .cons x (.cons y xs) => x ≤ y && (cons y xs).isSorted

/-- `x ≤ head of list` (vacuously true for nil). Helper for merge proofs. -/
def LeHead [LE α] (x : α) : List α → Prop
  | .nil => True
  | .cons y _ => x ≤ y

theorem Sorted.leHead [LE α] {x : α} {xs : List α} (h : Sorted (.cons x xs)) : LeHead x xs := by
  cases h with
  | singleton => trivial
  | cons _ _ _ hxy _ => exact hxy

theorem Sorted.tail [LE α] {x : α} {xs : List α} (h : Sorted (.cons x xs)) : Sorted xs := by
  cases h with
  | singleton => exact .nil
  | cons _ _ _ _ h => exact h

theorem Sorted.ofLeHead [LE α] {x : α} {xs : List α} (h : LeHead x xs) (hs : Sorted xs) :
    Sorted (.cons x xs) := by
  cases xs with
  | nil => exact .singleton x
  | cons y ys => exact .cons x y ys h hs

/-- Length of a list. -/
def List.length : List α → Nat
  | .nil => 0
  | .cons _ xs => xs.length + 1

/-- Merge two sorted lists into one sorted list. -/
def List.merge [LE α] [DecidableRel (α := α) (· ≤ ·)] : List α → List α → List α
  | .nil, r => r
  | .cons x xs, .nil => .cons x xs
  | .cons x xs, .cons y ys =>
    if x ≤ y then .cons x (merge xs (.cons y ys))
    else .cons y (merge (.cons x xs) ys)
termination_by l r => l.length + r.length
decreasing_by all_goals simp [List.length]

/-- `LeHead` is preserved by merge: if `z ≤` both heads, then `z ≤` the merge head. -/
theorem List.merge_leHead [LE α] [DecidableRel (α := α) (· ≤ ·)]
    (z : α) : ∀ (l r : List α), LeHead z l → LeHead z r → LeHead z (l.merge r)
  | .nil, _, _, hr => by simp only [List.merge]; exact hr
  | .cons _ _, .nil, hl, _ => by simp only [List.merge]; exact hl
  | .cons _ _, .cons _ _, hl, hr => by simp only [List.merge]; split <;> assumption

/-- Merging two sorted lists produces a sorted list. -/
theorem List.merge_sorted [LE α] [DecidableRel (α := α) (· ≤ ·)]
    (total : ∀ (a b : α), a ≤ b ∨ b ≤ a) :
    ∀ (l r : List α), Sorted l → Sorted r → Sorted (l.merge r)
  | .nil, _, _, hr => by simp only [List.merge]; exact hr
  | .cons _ _, .nil, hl, _ => by simp only [List.merge]; exact hl
  | .cons x xs, .cons y ys, hl, hr => by
    simp only [List.merge]
    split
    case isTrue hxy =>
      exact Sorted.ofLeHead
        (List.merge_leHead x xs (.cons y ys) hl.leHead hxy)
        (List.merge_sorted total xs (.cons y ys) hl.tail hr)
    case isFalse hxy =>
      exact Sorted.ofLeHead
        (List.merge_leHead y (.cons x xs) ys ((total x y).resolve_left hxy) hr.leHead)
        (List.merge_sorted total (.cons x xs) ys hl hr.tail)
termination_by l r => l.length + r.length
decreasing_by all_goals simp [List.length]

/-- Split a list into two halves (alternating elements). -/
def List.split : List α → List α × List α
  | .nil => (.nil, .nil)
  | .cons x .nil => (.cons x .nil, .nil)
  | .cons x (.cons y rest) =>
    let (l, r) := rest.split
    (.cons x l, .cons y r)

theorem List.split_length_sum : ∀ (l : List α),
    (l.split).1.length + (l.split).2.length = l.length
  | .nil => by rfl
  | .cons _ .nil => by rfl
  | .cons _ (.cons _ rest) => by
    simp [List.split, List.length]
    have ih := split_length_sum rest
    omega

theorem List.split_fst_lt (x y : α) (rest : List α) :
    ((List.cons x (.cons y rest)).split).1.length < (List.cons x (.cons y rest)).length := by
  simp [List.split, List.length]
  have := split_length_sum rest
  omega

theorem List.split_snd_lt (x y : α) (rest : List α) :
    ((List.cons x (.cons y rest)).split).2.length < (List.cons x (.cons y rest)).length := by
  simp [List.split, List.length]
  have := split_length_sum rest
  omega

/-- Merge sort — O(n log n). -/
def List.mergeSort [LE α] [DecidableRel (α := α) (· ≤ ·)] : List α → List α
  | .nil => .nil
  | .cons x .nil => .cons x .nil
  | .cons x (.cons y rest) =>
    let p := (List.cons x (.cons y rest)).split
    (p.1.mergeSort).merge (p.2.mergeSort)
termination_by l => l.length
decreasing_by
  · exact List.split_fst_lt x y rest
  · exact List.split_snd_lt x y rest

/-- Merge sort produces a sorted list. -/
theorem List.mergeSort_sorted [LE α] [DecidableRel (α := α) (· ≤ ·)]
    (total : ∀ (a b : α), a ≤ b ∨ b ≤ a) :
    ∀ (l : List α), Sorted l.mergeSort
  | .nil => by simp only [List.mergeSort]; exact .nil
  | .cons x .nil => by simp only [List.mergeSort]; exact .singleton x
  | .cons x (.cons y rest) => by
    simp only [List.mergeSort]
    exact List.merge_sorted total _ _
      (mergeSort_sorted total _)
      (mergeSort_sorted total _)
termination_by l => l.length
decreasing_by
  · exact List.split_fst_lt x y rest
  · exact List.split_snd_lt x y rest

/-- Sort a list (O(n log n) merge sort) with proof of sortedness. -/
def List.sort [LE α] [DecidableRel (α := α) (· ≤ ·)]
    (total : ∀ (a b : α), a ≤ b ∨ b ≤ a)
    (l : List α) : SortedList α :=
  ⟨l.mergeSort, List.mergeSort_sorted total l⟩

instance : ToString (List Nat) where
  toString l :=
    let rec go : List Nat → String
      | .nil => "nil"
      | .cons x xs => s!"{x} :: {go xs}"
    go l

instance : ToString (SortedList Nat) where
  toString sl := toString sl.list

def main : IO Unit := do
  let sorted := List.cons 1 (.cons 2 (.cons 3 .nil))
  IO.println s!"List:   {sorted}"
  IO.println s!"Sorted: {sorted.isSorted}"
  IO.println ""
  let unsorted := List.cons 3 (.cons 1 (.cons 2 .nil))
  IO.println s!"List:   {unsorted}"
  IO.println s!"Sorted: {unsorted.isSorted}"
  IO.println ""
  let unsortedSorted := unsorted.sort (fun a b => by omega)
  IO.println s!"List:   {unsortedSorted}"
  IO.println s!"Sorted: {unsortedSorted.list.isSorted}"

end SortList
