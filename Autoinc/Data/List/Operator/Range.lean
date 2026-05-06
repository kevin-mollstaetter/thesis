import Autoinc.Data.List.Change
import Autoinc.Data.Nat.Change
import Autoinc.Operator

namespace ΔList
namespace Range

variable (m : Type → Type) [MonadStateOf Nat m] -- input length
@[simp] def op [Monad m] : Operator Nat (List Nat) ΔNat (ΔList Nat ΔNat) m where
  f x := modifyGet (fun _ => (List.range x, x))
  Δf | .inc n => modifyGet (fun len => (.ins len (List.range' len n), len + n))
     | .dec n => modifyGet (fun len => (.del (len - n) n, len - n))

variable [ChangeMonad m] [LawfulChangeMonad m]
attribute [simp] LawfulChangeMonad.mprop_pure
theorem op_valid : (op m).valid := by
  intro x dx hvc
  match dx with
  | .inc n =>
    simp_all
    sorry
  | .dec n =>
    skip
    sorry

end Range
end ΔList

def testOp [Monad m] [BEq β]
  [Change α Δα]
  [Change β Δβ]
  (f : α → m β) (Δf : Δα → m Δβ) (a : α) (da : Δα) := do
  pure ((←f a) ⨁ (←Δf da) == (← f (a ⨁ da)))

abbrev UsedMonad := StateT Nat Id
abbrev f := (ΔList.Range.op UsedMonad).f
abbrev Δf := (ΔList.Range.op UsedMonad).Δf
abbrev input : Nat := 5
abbrev changedInput : ΔNat := .dec 3
#eval testOp (m := UsedMonad) f Δf input changedInput |>.run 0
