import Plausible
import Autoinc.Sequence

section Tree

-- sequence represented as a 2-3 tree
inductive Tree (α : Type) where
  | Empty
  | Leaf (val : α)
  | Node2 (height : Nat) (size : Nat) (left right : Tree α)
  | Node3 (height : Nat) (size : Nat) (left middle right : Tree α)
deriving BEq

def Tree.height : Tree α → Nat
  | Empty | Leaf _ => 0
  | Node2 h _ _ _ | Node3 h _ _ _ _ => h

def Tree.size : Tree α → Nat
  | Empty => 0
  | Leaf _ => 1
  | Node2 _ size _ _ | Node3 _ size _ _ _ => size

-- assumption: l.height == r.height
def mkNode2 (l r : Tree α) : Tree α :=
  .Node2 (l.height + 1) (l.size + r.size) l r

-- assumption: l.height == m.height == r.height
def mkNode3 (l m r : Tree α) : Tree α :=
  .Node3 (l.height + 1) (l.size + m.size + r.size) l m r

def combine : List (Tree α) → List (Tree α)
  | [a, b] => [mkNode2 a b]
  | [a, b, c] => [mkNode3 a b c]
  | [a, b, c, d] => [mkNode2 a b, mkNode2 c d]
  | _ => panic! "invalid level up state"

def mergeToSameHeight (a b : Tree α) : List (Tree α) :=
  let heightA := a.height
  let heightB := b.height
  if heightA < heightB then
    -- merge A into B
    match b with
    | .Node2 _ _ bl br => combine (mergeToSameHeight a bl ++ [br])
    | .Node3 _ _ bl bm br => combine (mergeToSameHeight a bl ++ [bm, br])
    | _ => panic! "invalid"
  else if heightA > heightB then
    -- merge B into A
    match a with
    | .Node2 _ _ al ar => combine ([al] ++ mergeToSameHeight ar b)
    | .Node3 _ _ al am a3 => combine ([al, am] ++ mergeToSameHeight a3 b)
    | _ => panic! "invalid"
  else
    [a, b]

def Tree.merge : Tree α → Tree α → Tree α
  | a, Empty => a
  | Empty, b => b
  | a, b => match mergeToSameHeight a b with
    | [t] => t
    | [t, u] => mkNode2 t u
    | _ => .Empty -- invalid state, TODO: find cleaner solution

/-- splits the tree at an index -/
def Tree.split (i : Nat) : Tree α → (Tree α) × (Tree α)
  | Empty => (Empty, Empty)
  | Leaf x => if i == 0 then (Empty, Leaf x) else (Leaf x, Empty)
  | Node2 _ _ l r =>
    let sizeL := l.size
    if i < sizeL then
      -- split index is in left branch
      let (l1, l2) := l.split i
      (l1, l2.merge r)
    else
      -- split index is in right branch
      let (r1, r2) := r.split (i - sizeL)
      (l.merge r1, r2)
  | Node3 _ _ l m r =>
    let sizeL := l.size
    if i < sizeL then
      -- split index is in left branch
      let (l1, l2) := l.split i
      (l1, l2.merge (mkNode2 m r))
    else
      let sizeM := m.size
      let i' := i - sizeL
      if i' < sizeM then
        -- split index is in middle branch
        let (m1, m2) := m.split i'
        (l.merge m1, m2.merge r)
      else
        -- split index is in right branch
        let (r1, r2) := r.split (i' - sizeM)
        (l.merge (mkNode2 m r1), r2)

def Tree.insert (t : Tree α) (i : Nat) (x : α) : Tree α :=
  let (l, r) := t.split i
  l.merge (Leaf x) |>.merge r

def Tree.delete (t : Tree α) (i : Nat) : Tree α :=
  let (l, r) := t.split i
  let (_, r2) := r.split 1
  l.merge r2

def Tree.push (t : Tree α) (x : α) : Tree α :=
  t.insert t.size x

def Tree.fromList (xs : List α) : Tree α :=
  xs.foldl (fun t x => t.push x) .Empty

def Tree.toList (t : Tree α) : List α :=
  prepend t []
    where
  prepend : Tree α → List α → List α
  | Empty, xs => xs
  | Leaf x, xs => x :: xs
  | Node2 _ _ l r, xs => prepend l (prepend r xs)
  | Node3 _ _ l m r, xs => prepend l (prepend m (prepend r xs))

-- is fold the correct term here?
def Tree.foldl (t : Tree α) (f : β → α → β) (init : β) :=
  match t with
  | Empty => init
  | Leaf x => f init x
  | Node2 _ _ l r => foldl l f (foldl r f init)
  | Node3 _ _ l m r => foldl l f (foldl m f (foldl r f init))

def Tree.count [BEq α] (t : Tree α) (x : α) : Nat :=
  t.foldl (fun acc y => if x == y then acc + 1 else acc) 0

def Tree.getRange (t : Tree α) (i n : Nat) : Tree α :=
  let (_, r) := t.split i
  r.split n |>.1

def Tree.insertList (t : Tree α) (i : Nat) (xs : List α) : Tree α :=
  let txs := Tree.fromList xs
  let (l, r) := t.split i
  l.merge txs |>.merge r

def Tree.deleteRange (t : Tree α) (i n : Nat) : Tree α :=
  let (l, r) := t.split i
  let (_, rr) := r.split n
  l.merge rr

def Tree.fold (t : Tree α) (fempty : β) (fleaf : α → β) (fnode2 : β → β → β) (fnode3 : β → β → β → β) :=
  match t with
  | Empty => fempty
  | Leaf x => fleaf x
  | Node2 _ _ l r =>
    fnode2
      (l.fold fempty fleaf fnode2 fnode3)
      (r.fold fempty fleaf fnode2 fnode3)
  | Node3 _ _ l m r =>
    fnode3
      (l.fold fempty fleaf fnode2 fnode3)
      (m.fold fempty fleaf fnode2 fnode3)
      (r.fold fempty fleaf fnode2 fnode3)

def Tree.patchWith (t : Tree α) (f : α → β → α) (ds : List β) : Tree α :=
  -- TODO: look for more optimal ways (its gonna be O(n) either way but maybe we can reduce it by a constant factor of 2-3)
  Tree.fromList <| t.toList |>.zipWith f ds

instance : Sequence α (Tree α) where
  fromList := Tree.fromList
  toList := Tree.toList
  insert := Tree.insert
  delete := Tree.delete
  splitAt t i := t.split i
  length := Tree.size
  count := Tree.count
  getRange := Tree.getRange
  insertList := Tree.insertList
  deleteRange := Tree.deleteRange
  concat := Tree.merge
  patchWith := Tree.patchWith

instance : Inhabited (Tree α) where
  default := .Empty

end Tree

namespace Tree.Tests

open Plausible in
instance : Arbitrary (Fin n) where
  arbitrary := do
    let size ← Gen.getSize -- the target size
    if h: size == 0 || n <= 0
    then Except.error (GenError.genError "impossible to generate value")
    else
      let k ← Gen.chooseNatLt 0 n (by grind)
      return ⟨k, by grind⟩

open Plausible in
instance : Shrinkable (Fin n) where

abbrev α := Nat

-- toList is inverse to fromList
example (xs : List α) :
  (Tree.fromList xs |>.toList) == xs
:= by plausible

-- tree has correct size
example (xs : List α) :
  (Tree.fromList xs |>.size) == xs.length
:= by plausible

-- push works
example (xs : List α) (x : α) :
  let t := Tree.fromList xs |>.push x
  let xs' := xs ++ [x]
  t.toList == xs'
:= by plausible

-- insert works
example (xs : List α) (i : Fin (xs.length)) (x : α) :
  let t := Tree.fromList xs |>.insert i x
  let xs' := xs.insertIdx i x
  t.toList == xs'
:= by plausible

-- delete works
example (xs : List α) (i : Fin (xs.length)) :
  let t := Tree.fromList xs |>.delete i
  let (xs₁, xs₂) := xs.splitAt i
  t.toList == xs₁ ++ xs₂.tail
:= by plausible

end Tree.Tests
