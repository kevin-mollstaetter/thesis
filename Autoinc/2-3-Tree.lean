import Plausible

section
-- 2-3 tree containing elements of type α, ported from https://sortingsearching.com/2020/05/23/2-3-trees.html
inductive Tree (α : Type) where
  | Empty
  | Leaf (val : α)
  | Node2 (height : Nat) (smallest : α) (left right : Tree α)
  | Node3 (height : Nat) (smallest : α) (left middle right : Tree α)
deriving Repr, BEq

variable [Inhabited α]
def Tree.height : Tree α → Nat
  | Empty | Leaf _ => 0
  | Node2 h _ _ _ | Node3 h _ _ _ _ => h

instance : Inhabited (Tree α) where
  default := .Empty

def Tree.smallest! : Tree α → α
  | Empty => panic! "no"
  | Leaf x => x
  | Node2 _ s _ _ | Node3 _ s _ _ _ => s

def Tree.node2 (l r : Tree α) : Tree α :=
  Node2 (l.height + 1) (l.smallest!) l r

def Tree.node3 (l m r : Tree α) : Tree α :=
  Node3 (l.height + 1) (l.smallest!) l m r

def Tree.levelUp : List (Tree α) → List (Tree α)
  | [a, b] => [node2 a b]
  | [a, b, c] => [node3 a b c]
  | [a, b, c, d] => [node2 a b, node2 c d]
  | _ => panic! "invalid level up state"

def Tree.mergeToSameHeight (a b : Tree α) : List (Tree α) :=
  let ha := height a
  let hb := height b
  if ha < hb then
    match b with
    | Node2 _ _ b1 b2 => levelUp (mergeToSameHeight a b1 ++ [b2])
    | Node3 _ _ b1 b2 b3 => levelUp (mergeToSameHeight a b1 ++ [b2, b3])
    | _ => []
  else if ha > hb then
    match a with
    | Node2 _ _ a1 a2 => levelUp ([a1] ++ mergeToSameHeight a2 b)
    | Node3 _ _ a1 a2 a3 => levelUp ([a1, a2] ++ mergeToSameHeight a3 b)
    | _ => []
  else
    [a, b]

def Tree.merge : Tree α → Tree α → Tree α
  | a, Empty => a
  | Empty, b => b
  | a, b =>
    match mergeToSameHeight a b with
    | [t] => t
    | [t, u] => node2 t u
    | _ => panic! "invalid merge state"

def Tree.split (p : α → Bool) : Tree α → (Tree α) × (Tree α)
  | Empty => (Empty, Empty)
  | Leaf x => if p x then (Empty, Leaf x) else (Leaf x, Empty)
  | Node2 _ _ a b =>
    if p (b.smallest!) then
      let (a1, a2) := split p a
      (a1, merge a2 b)
    else
      let (b1, b2) := split p b
      (merge a b1, b2)
  | Node3 _ _ a b c =>
    if p b.smallest! then
      let (a1, a2) := split p a
      (a1, merge a2 (node2 b c))
    else if p c.smallest! then
      let (b1, b2) := split p b
      (merge a b1, merge b2 c)
    else
      let (c1, c2) := split p c
      (merge (node2 a b) c1, c2)

def Tree.contains [Ord α] (t : Tree α) (x : α) : Bool :=
  match split (fun y => Ord.compare x y |>.isLE) t with
  | (_, Empty) => False
  | (_, a2) => Ord.compare a2.smallest! x |>.isEq

def Tree.insert [Ord α] (t : Tree α) (x : α) : Tree α :=
  let (a1, a2) := split (fun y => Ord.compare x y |>.isLE) t
  a1.merge (Leaf x) |>.merge a2

def Tree.delete [Ord α] (t : Tree α) (x : α) : Tree α :=
  let (a1, a2) := split (fun y => Ord.compare x y |>.isLE) t
  let (_, a3) := split (fun y => Ord.compare x y |>.isLT) t
  merge a1 a3

def Tree.fromList [Ord α] (xs : List α) : Tree α :=
  xs.foldl insert Empty

def Tree.prepend : Tree α → List α → List α
  | Empty, xs => xs
  | Leaf x, xs => x :: xs
  | Node2 _ _ a b, xs => prepend a (prepend b xs)
  | Node3 _ _ a b c, xs => prepend a (prepend b (prepend c xs))

def Tree.toList (t : Tree α) : List α :=
  prepend t []

def fromListToList [Ord α] (xs : List α) : List α :=
  Tree.fromList xs |>.toList

end

example (xs : List Nat) :
  let xs' := xs.mergeSort
  (fromListToList xs' == xs') := by plausible

example (xs : List Nat) (x : Nat) :
  let t := Tree.fromList xs
  let t' := t.insert x
  t'.toList == (x :: xs).mergeSort := by plausible

example (xs : List Nat) (ys : List Nat) :
  let tx := Tree.fromList xs
  let t' := ys.foldl (fun t y => t.insert y) tx
  t'.toList == (xs ++ ys).mergeSort := by plausible
