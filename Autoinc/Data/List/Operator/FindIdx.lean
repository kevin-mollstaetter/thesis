import Autoinc.Data.List.Change
import Autoinc.Operator
import Autoinc.Lazy

namespace ΔList
namespace FindIdx

#print List.findIdx

variable {α Δα} [Change α Δα]
variable (m : Type → Type)
variable [MonadReaderOf (α → Bool) m] -- the predicate
variable [MonadStateOf Nat m] -- the idx (= #elements in front of the element satisfying the predicate)
variable [LazyMonadStateOf (List α) m]

/-
Explanation
In all cases, if i > currIdx then the modification doesn't affect the idx as the list is searched from left to right
Let xs be the list
Let x be the element that satisifes p
Let oldIdx be the idx of x in xs
if i ≤ currIdx then
| .ins i ys =>
  1. x ∈ ys: in front of the new x are ys.findIdx x + i elements => newIdx = i + ys.findIdx x
  2. x ∉ ys: x is pushed back by ys.length elements => newIdx = oldIdx + ys.length
| .del i n =>
  1. i + n > oldIdx => x is deleted => newIdx = xs'.findIdx p
  2. i + n ≤ oldIdx => x is not deleted => newIdx = oldIdx - n
| .upd i n =>
  update changes the elements before the oldIdx, so everything has to be rechecked=> newIdx = xs'.findIdx p
-/
@[simp] def Δf [Monad m] (dx : ΔList α Δα) : m ΔNat := do
  let oldIdx ← getThe Nat
  lazyModify (fun xs : List α => xs ⨁ dx)
  match dx with
  | .ins i ys =>
    if i > oldIdx then
      pure <| .inc 0
    else
      let p ← read
      modifyGetThe Nat (fun oldIdx =>
        match ys.findIdx? p with
        | some idx => let newIdx := i + idx; (newIdx ⊖ oldIdx, newIdx)
        | none => let dtIdx := .inc ys.length; (dtIdx, oldIdx ⨁ dtIdx)
      )
  | .del i n =>
    if i > oldIdx then
      pure <| .inc 0
    else
      if i + n > oldIdx then
        let newIdx := (←getThe (List α)).findIdx (←read)
        set newIdx
        pure <| newIdx ⊖ oldIdx
      else
        let dtIdx := .dec n
        set <| oldIdx ⨁ dtIdx
        pure dtIdx
  | .upd i _ =>
    if i > oldIdx then
      pure <| .inc 0
    else
      let newIdx := (←getThe (List α)).findIdx (←read)
      set newIdx
      pure <| newIdx ⊖ oldIdx

@[simp] def op [Monad m] : Operator (List α) Nat (ΔList α Δα) ΔNat m where
  f x := do
    let p ← read
    lazyModify (fun _ => x)
    modifyGetThe Nat (fun _ => let idx := x.findIdx p; (idx, idx))
  Δf := Δf m

end FindIdx
end ΔList

def testOp [Monad m] [BEq β]
  [Change α Δα]
  [Change β Δβ]
  (f : α → m β) (Δf : Δα → m Δβ) (a : α) (da : Δα) := do
  pure ((←f a) ⨁ (←Δf da) == (← f (a ⨁ da)))

def testOp2 [Monad m] [BEq β]
  [Change α Δα]
  [Change β Δβ]
  [ToString α]
  [ToString Δα]
  [ToString β]
  [ToString Δβ]
  (f : α → m β) (Δf : Δα → m Δβ) (a : α) (da : Δα) := do
  let fst ← f a
  let snd ← Δf da
  let firstResult := fst ⨁ snd
  let a_plus_da := a ⨁ da
  let secondResult := (← f a_plus_da)
  pure s!"  f a ⨁ Δf da \n= f {a} ⨁ Δf {da} \n= {fst} ⨁ {snd} \n= {firstResult} =?= {secondResult} \n= f {a_plus_da} \n= f a ⨁ da"

abbrev α := Nat
abbrev Δα := ΔNat
abbrev UsedMonad := LazyStateT (List α) (StateT Nat (ReaderT (α → Bool) Id))
abbrev f := (ΔList.FindIdx.op UsedMonad (α := α) (Δα := Δα)).f
abbrev Δf := (ΔList.FindIdx.op UsedMonad (α := α) (Δα := Δα)).Δf
abbrev input : List α := [1, 2, 3, 4, 5]
abbrev inputChange : ΔList α Δα := .upd 1 [.dec 3, .inc 2, .dec 1]--[9, 3, 3, 1, 2]
abbrev x : α := 1
abbrev dx : Δα := .dec 1
abbrev change : ΔList α Δα := .upd 0 [.inc 1, .inc 2, .dec 3]
#eval input.count x
#eval testOp2 (m := UsedMonad) f Δf input change |>.run default |>.run default |>.run (· == x) |>.fst.fst.toFormat
