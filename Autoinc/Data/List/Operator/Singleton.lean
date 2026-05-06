import Autoinc.Change
import Autoinc.Operator
import Autoinc.Data.List.Change
import Plausible

namespace ΔList
namespace Singleton

#print List.singleton

variable {α : Type} {Δα : Type} [Change α Δα]
variable (m : Type → Type)
@[simp] def op [Monad m] : Operator α (List α) Δα (ΔList α Δα) m where
  f x := pure <| List.singleton x
  Δf dx := pure <| .upd 0 [dx]

variable [ChangeMonad m] [LawfulChangeMonad m]
attribute [simp] LawfulChangeMonad.mprop_pure
theorem op_valid [Monad m] : (op (α := α) (Δα := Δα) m).valid := by
  intro x dx hvc
  simp_all [List.singleton]
  sorry

theorem op_correct : (op (α := α) (Δα := Δα) m).correct := by
  intro x dx hvc
  simp_all
  congr

end Singleton
end ΔList
