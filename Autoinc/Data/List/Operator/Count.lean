import Autoinc.Data.List.Change
import Autoinc.Data.Nat.Change
import Autoinc.Operator
import Autoinc.Partial
import Autoinc.Lazy
import Autoinc.Data.Bool.Change
import Autoinc.Sequence
import Autoinc.SequenceTree
import Plausible

namespace ΔList
namespace Count

#print List.count

variable {α Δα : Type} [Change α Δα]
variable (m : Type → Type)
variable [MonadStateOf (α × Nat) m] -- the element to count and its count
variable {γ : Type} [Sequence α γ] -- γ is the internal list representation
variable [LazyMonadStateOf γ m] -- the input list
variable [BEq α]

@[simp] def countFrom [Sequence α γ] (xs : γ) (i : Nat) (x : α) (n : Nat) :=
  let ys := Sequence.getRange xs i n
  Sequence.count ys x

@[simp] def δf_1 [Monad m] (dxs : ΔList α Δα) : m ΔNat :=
  match dxs with
  | ins _ ys => do
    lazyModify (fun xs : γ => xs ⨁ dxs)
    modifyGetThe (α × Nat) (fun (x, oldOcc) =>
      let newOcc := ΔNat.inc <| ys.count x
      (newOcc, (x, oldOcc ⨁ newOcc))
    )
  | del i n => do
    let xs ← getThe γ
    lazyModify (fun xs : γ => xs ⨁ dxs)
    modifyGetThe (α × Nat) (fun (x, oldOcc) =>
      let dtOcc := .dec <| countFrom xs i x n
      (dtOcc, (x, oldOcc ⨁ dtOcc))
    )
  | upd i ds => do
    let xs ← getThe γ
    let xs' ← modifyGetThe γ (fun xs =>
      let xs' := xs ⨁ dxs
      (xs', xs')
    )
    let len := ds.length
    modifyGetThe (α × Nat) (fun (x, oldOcc) =>
      let occInSegment := countFrom xs i x len
      let newOcc := countFrom xs' i x len
      let dtOcc := newOcc ⊖ occInSegment
      (dtOcc, (x, oldOcc ⨁ dtOcc))
    )

@[simp] def δf_2 [Monad m] (dx : Δα) : m ΔNat := do
  let xs ← getThe γ
  modifyGetThe (α × Nat) (fun (x, oldOcc) =>
    let x' := x ⨁ dx
    let newOcc := Sequence.count xs x'
    (newOcc ⊖ oldOcc, (x', newOcc))
  )

@[simp] def partial_op [Monad m] : PartialOperator (List α) α Nat (ΔList α Δα) Δα ΔNat m where
  f xs x := do
    lazyModify (fun _ => Sequence.fromList (γ := γ) xs)
    let count := xs.count x
    set (x, count)
    pure <| count
  δf_1 := δf_1 m (γ := γ)
  δf_2 := δf_2 m (α := α) (γ := γ)

def op [Monad m] := (partial_op (α:=α) (Δα:=Δα) (γ := γ) m).toOperator

-- variable [ChangeMonad m] [LawfulChangeMonad m]
-- theorem op_valid : (op (α := α) (Δα := Δα) m).valid := by
--   sorry

-- theorem op_correct : (op (α := α) (Δα := Δα) m).correct := by
--   sorry

-- def spec : (op (α := α) (Δα := Δα) m).spec where
--   valid := op_valid m
--   correct := op_correct m

end Count
end ΔList

def testOpFormat [Monad m] [BEq β]
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

namespace Count.Tests

open ChangeMonad
def testOp
  [Monad m] [ChangeMonad m]
  [BEq β]
  [Change α Δα]
  [Change β Δβ]
  (f : α → m β) (Δf : Δα → m Δβ) (a : α) (da : Δα) := do
  pure ((←f a) ⨁ (←Δf da) == (← f (a ⨁ da)))

def testOpMulti
  [Monad m] [ChangeMonad m]
  [BEq β]
  [Change α Δα]
  [Change β Δβ]
  (f : α → m β) (Δf : Δα → m Δβ) (a : α) (das : List Δα) := do
  let mut acc ← f a
  for da in das do
    acc := acc ⨁ (←Δf da)
  let a' := das.foldl (fun a' da => a' ⨁ da) a
  pure (acc == (←f a'))

abbrev α := Nat
abbrev Δα := ΔNat
abbrev γ := Tree α
abbrev UsedMonad := LazyStateT γ (StateT (α × Nat) Id)

abbrev f := (ΔList.Count.op UsedMonad (α := α) (Δα := Δα) (γ := γ)).f
abbrev Δf := (ΔList.Count.op UsedMonad (α := α) (Δα := Δα) (γ := γ)).Δf

def testOpSingleChange (input : List α) (x : α) (change : ΔProd (ΔList α Δα) Δα) :=
  testOp (m := UsedMonad) f Δf (input, x) change |>.run default |>.run default |>.fst.fst

def testOpMultiChange (input : List α) (x : α) (changes : List (ΔProd (ΔList α Δα) Δα)) :=
  testOpMulti (m := UsedMonad) f Δf (input, x) changes |>.run default |>.run default |>.fst.fst

-- single list change
example (input : List α) (x : α) (change : ΔList α Δα) :
  testOpSingleChange input x (ΔProd._1 change)
:= by plausible

-- single x change
example (input : List α) (x : α) (change : Δα) :
  testOpSingleChange input x (ΔProd._2 change)
:= by plausible

-- multiple list changes
example (input : List α) (x : α) (changes : List (ΔList α Δα)) :
  testOpMultiChange input x (changes.map (ΔProd._1 ·))
:= by plausible

-- multiple x changes
example (input : List α) (x : α) (changes : List Δα) :
  testOpMultiChange input x (changes.map (ΔProd._2 ·))
:= by plausible

-- mixed changes (list + count)
example (input : List α) (x : α) (changes : List (ΔProd (ΔList α Δα) Δα)) :
  testOpMultiChange input x changes
:= by plausible

end Count.Tests
