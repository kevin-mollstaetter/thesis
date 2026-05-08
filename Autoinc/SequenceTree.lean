import Plausible
import Autoinc.Sequence

section SequenceTree

-- sequence represented as a 2-3 tree
inductive SequenceTree (α : Type) where
  | Empty
  | Leaf (val : α)
  | Node2 (height : Nat) (size : Nat) (left right : SequenceTree α)
  | Node3 (height : Nat) (size : Nat) (left middle right : SequenceTree α)
deriving BEq, Inhabited

def SequenceTree.height : SequenceTree α → Nat
  | Empty | Leaf _ => 0
  | Node2 h _ _ _ | Node3 h _ _ _ _ => h

def SequenceTree.size : SequenceTree α → Nat
  | Empty => 0
  | Leaf _ => 1
  | Node2 _ size _ _ | Node3 _ size _ _ _ => size

-- assumption: l.height == r.height
def mkNode2 (l r : SequenceTree α) : SequenceTree α :=
  .Node2 (l.height + 1) (l.size + r.size) l r

-- assumption: l.height == m.height == r.height
def mkNode3 (l m r : SequenceTree α) : SequenceTree α :=
  .Node3 (l.height + 1) (l.size + m.size + r.size) l m r

inductive OneOrTwo (α : Type) where
  | One (a : α)
  | Two (a b : α)
deriving Inhabited

-- assumption a and b are not .Empty and well formed
def mergeToSameHeight (a b : SequenceTree α) : OneOrTwo (SequenceTree α) :=
  let heightA := a.height
  let heightB := b.height
  if heightA < heightB then
    -- merge a into b
    -- b must be a Node2 or Node3 as b.height > a.height ≥ 1
    match b with
    | .Node2 _ _ l r =>
      match mergeToSameHeight a l with
      | .One t => .One <| mkNode2 t r
      | .Two t₁ t₂ => .One <| mkNode3 t₁ t₂ r
    | .Node3 _ _ l m r =>
      match mergeToSameHeight a l with
      | .One t => .One <| mkNode3 t m r
      | .Two t₁ t₂ => .Two (mkNode2 t₁ t₂) (mkNode2 m r)
    | _ => panic! "a and b must be non empty and well formed!"
  else if heightA > heightB then
    -- merge b into a
    -- a must be a Node2 or Node3 as a.height > b.height ≥ 1
    match a with
    | .Node2 _ _ l r =>
      match mergeToSameHeight r b with
      | .One t => .One <| mkNode2 l t
      | .Two t₁ t₂ => .One <| mkNode3 l t₁ t₂
    | .Node3 _ _ l m r =>
      match mergeToSameHeight r b with
      | .One t => .One <| mkNode3 l m t
      | .Two t₁ t₂ => .Two (mkNode2 l m) (mkNode2 t₁ t₂)
    | _ => panic! "a and b must be non empty and well formed!"
  else
    .Two a b

def SequenceTree.merge : SequenceTree α → SequenceTree α → SequenceTree α
  | a, Empty => a
  | Empty, b => b
  | a, b =>
    match mergeToSameHeight a b with
    | .One a => a
    | .Two a b => mkNode2 a b

def SequenceTree.split (i : Nat) : SequenceTree α → (SequenceTree α) × (SequenceTree α)
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

def SequenceTree.insert (t : SequenceTree α) (i : Nat) (x : α) : SequenceTree α :=
  let (l, r) := t.split i
  l.merge (Leaf x) |>.merge r

def SequenceTree.delete (t : SequenceTree α) (i : Nat) : SequenceTree α :=
  let (l, r) := t.split i
  let (_, r2) := r.split 1
  l.merge r2

def SequenceTree.push (t : SequenceTree α) (x : α) : SequenceTree α :=
  t.insert t.size x

def fromListAux (remaining : List (SequenceTree α)) (acc: List (SequenceTree α)) (flip : Bool) : SequenceTree α :=
  match remaining, acc with
  | [], _ => .Empty
  | [a], _ => a
  | [a, b], [] => if flip then mkNode2 b a else mkNode2 a b
  | [a, b], acc =>
    let node := if flip then mkNode2 b a else mkNode2 a b
    fromListAux (node :: acc) [] !flip
  | [a, b, c], [] =>
    if flip then mkNode3 c b a else mkNode3 a b c
  | [a, b, c], acc =>
    let node := if flip then mkNode3 c b a else mkNode3 a b c
    fromListAux (node :: acc) [] !flip
  | [a, b, c, d], [] =>
    let node₁ := if flip then mkNode2 b a else mkNode2 a b
    let node₂ := if flip then mkNode2 d c else mkNode2 c d
    if flip then mkNode2 node₂ node₁ else mkNode2 node₁ node₂
  | [a, b, c, d], acc =>
    let node₁ := if flip then mkNode2 b a else mkNode2 a b
    let node₂ := if flip then mkNode2 d c else mkNode2 c d
    fromListAux (node₂ :: node₁ :: acc) [] !flip
  | a :: b :: c :: remaining, acc =>
    let node := if flip then mkNode3 c b a else mkNode3 a b c
    fromListAux remaining (node :: acc) flip
termination_by remaining.length + acc.length

def SequenceTree.fromList (xs : List α) : SequenceTree α :=
  fromListAux (xs.map (.Leaf ·)) [] false

def SequenceTree.fromList' (xs : List α) : SequenceTree α :=
  xs.foldl (fun t x => t.push x) .Empty -- this is horribly slow

def SequenceTree.toList (t : SequenceTree α) : List α :=
  prepend t []
    where
  prepend : SequenceTree α → List α → List α
  | Empty, xs => xs
  | Leaf x, xs => x :: xs
  | Node2 _ _ l r, xs => prepend l (prepend r xs)
  | Node3 _ _ l m r, xs => prepend l (prepend m (prepend r xs))

-- TODO: is fold the correct term here?
def SequenceTree.foldl (t : SequenceTree α) (f : β → α → β) (init : β) :=
  match t with
  | Empty => init
  | Leaf x => f init x
  | Node2 _ _ l r => foldl l f (foldl r f init)
  | Node3 _ _ l m r => foldl l f (foldl m f (foldl r f init))

partial def foldlTRAux (f : β → α → β) (init : β) (remaining : List (SequenceTree α)) : β :=
  match remaining with
  | [] => init
  | .Empty :: remaining => foldlTRAux f init remaining
  | .Leaf x :: remaining => foldlTRAux f (f init x) remaining
  | .Node2 _ _ l r :: remaining => foldlTRAux f init (l :: r :: remaining)
  | .Node3 _ _ l m r :: remaining => foldlTRAux f init (l :: m :: r :: remaining)

def SequenceTree.foldlTR (t : SequenceTree α) (f : β → α → β) (init : β) :=
  foldlTRAux f init [t]

def SequenceTree.count [BEq α] (t : SequenceTree α) (x : α) : Nat :=
  t.foldlTR (fun acc y => if x == y then acc + 1 else acc) 0

def SequenceTree.getRange (t : SequenceTree α) (i n : Nat) : SequenceTree α :=
  let (_, r) := t.split i
  r.split n |>.1

def SequenceTree.insertList (t : SequenceTree α) (i : Nat) (xs : List α) : SequenceTree α :=
  let txs := SequenceTree.fromList xs
  let (l, r) := t.split i
  l.merge txs |>.merge r

def SequenceTree.deleteRange (t : SequenceTree α) (i n : Nat) : SequenceTree α :=
  let (l, r) := t.split i
  let (_, rr) := r.split n
  l.merge rr

def SequenceTree.fold (t : SequenceTree α) (fempty : β) (fleaf : α → β) (fnode2 : β → β → β) (fnode3 : β → β → β → β) :=
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

def SequenceTree.patchWith (t : SequenceTree α) (f : α → β → α) (ds : List β) : SequenceTree α :=
  let rec helper : SequenceTree α → List β → ((SequenceTree α) × List β)
    | t, [] => (t, [])
    | Empty, ds => (Empty, ds)
    | Leaf x, d :: ds => (Leaf (f x d), ds)
    | Node2 h s l r, ds =>
      let (patchedL, ds') := helper l ds
      let (patchedR, ds'') := helper r ds'
      (Node2 h s patchedL patchedR, ds'')
    | Node3 h s l m r, ds =>
      let (patchedL, ds') := helper l ds
      let (patchedM, ds'') := helper m ds'
      let (patchedR, ds''') := helper r ds''
      (Node3 h s patchedL patchedM patchedR, ds''')
  helper t ds |>.1

instance : Sequence α (SequenceTree α) where
  fromList := SequenceTree.fromList
  toList := SequenceTree.toList
  insert := SequenceTree.insert
  delete := SequenceTree.delete
  splitAt t i := t.split i
  length := SequenceTree.size
  count := SequenceTree.count
  getRange := SequenceTree.getRange
  insertList := SequenceTree.insertList
  deleteRange := SequenceTree.deleteRange
  concat := SequenceTree.merge
  patchWith := SequenceTree.patchWith

end SequenceTree

namespace SequenceTree.Tests

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
  (SequenceTree.fromList xs |>.toList) == xs
:= by plausible

-- tree has correct size
example (xs : List α) :
  (SequenceTree.fromList xs |>.size) == xs.length
:= by plausible

-- push works
example (xs : List α) (x : α) :
  let t := SequenceTree.fromList xs |>.push x
  let xs' := xs ++ [x]
  t.toList == xs'
:= by plausible

-- insert works
example (xs : List α) (i : Fin (xs.length)) (x : α) :
  let t := SequenceTree.fromList xs |>.insert i x
  let xs' := xs.insertIdx i x
  t.toList == xs'
:= by plausible

-- delete works
example (xs : List α) (i : Fin (xs.length)) :
  let t := SequenceTree.fromList xs |>.delete i
  let (xs₁, xs₂) := xs.splitAt i
  t.toList == xs₁ ++ xs₂.tail
:= by plausible

-- foldlTR = foldl
example (xs : List α) :
  let t := SequenceTree.fromList xs
  let f := (fun acc y => if x == y then acc + 1 else acc)
  let resTR := t.foldlTR f 0
  let resNTR := t.foldl f 0
  resTR == resNTR
:= by plausible

-- fromList = fromList'
example (xs : List α) :
  (SequenceTree.fromList xs |>.toList) == (SequenceTree.fromList' xs |>.toList)
:= by plausible

end SequenceTree.Tests
