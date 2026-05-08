import Autoinc.Change
import Autoinc.Data.List.Change
#check Membership
universe u v in
class Sequence (α : outParam (Type u)) (γ : Type v) where
  fromList : List α → γ
  toList : γ → List α
  insert : γ → Nat → α → γ
  delete : γ → Nat → γ
  splitAt : γ → Nat → (γ × γ)
  length : γ → Nat
  count : [BEq α] → γ → α → Nat
  getRange : γ → Nat → Nat → γ -- starting from Nat get Nat elements
  insertList : γ → Nat → List α → γ
  deleteRange : γ → Nat → Nat → γ
  concat : γ → γ → γ
  patchWith {β : Type u} : γ → (α → β → α) → List β → γ

instance : Sequence α (List α) where
  fromList := id
  toList := id
  insert := List.insertIdx
  delete xs i :=
    let (xs₁, xs₂) := xs.splitAt i
    xs₁ ++ xs₂.tail
  splitAt xs i := xs.splitAt i
  length := List.length
  count xs x := xs.count x
  getRange xs i n := xs.drop i |>.take n
  insertList xs i ys :=
    let (xs₁, xs₂) := List.splitAt i xs
    xs₁ ++ ys ++ xs₂
  deleteRange xs i n :=
    let (xs₁, xs₂) := List.splitAt i xs
    xs₁ ++ xs₂.drop n
  concat := HAppend.hAppend
  patchWith xs f ys := xs.zipWith f ys

instance [Sequence α γ] : Append γ where
  append xs ys := Sequence.concat xs ys

instance [ToString α] [Sequence α γ] : ToString γ where
  toString s := ToString.toString (Sequence.toList s)

instance [Change α Δα] [Sequence α γ] : Change γ (ΔList α Δα) where
  patch s
    | .ins i ys => Sequence.insertList s i ys
    | .del i n => Sequence.deleteRange s i n
    | .upd i ds =>
      let (xs₁, xs₂) := Sequence.splitAt s i
      let (ys, zs) := Sequence.splitAt xs₂ ds.length
      let ys' := Sequence.patchWith ys Change.patch ds
      xs₁ ++ ys' ++ zs
  valid s
    | .ins i ys => ys.isEmpty ∨ i ≤ Sequence.length s
    | .del i n => n = 0 ∨ i + n ≤ Sequence.length s
    | .upd i ds => ds.isEmpty ∨
        i + ds.length ≤ Sequence.length s ∧
          let ys := Sequence.getRange s i ds.length
          List.Forall₂ Change.valid (Sequence.toList ys) ds
