import YM.Integration.WilsonReceivedDepositedOrbitalEuler
import YM.Integration.WilsonReceivedDepositedOrbitalColumns

/-! The measured thermal numerator and its squarefree marked logarithm satisfy
the original finite marker Euler equation in the whole thermal algebra. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalEquation
open Finset Marker Multi Comparison.RG02 Comparison.RG02.Order
open WilsonCoeffUV.Wheel.Mark Extra.Trajectories
open WilsonReceivedDepositedOrbitalMode (face)
open WilsonReceivedDepositedOrbitalColumns (row)
open WilsonReceivedDepositedOrbitalEuler (count euler)
open scoped Classical BigOperators
variable {V:Type}[Fintype V][DecidableEq V]{r:ℕ}
local notation "J" => Stock.census V

def physical {V:Type} (r:ℕ):V⊕Fin r→ℂ:=Sum.elim (fun _=>1) (fun _=>0)

theorem graded (x:Grade (J) r):
    row (euler (physical r) x)=dial (row x):=by
  funext s
  apply Marker.Poly.ext
  intro t
  change (∑j∈s.disjSum t.val,physical r j)*x.part (Join.pair (face s) t)=
    (s.card • row x s).part t
  rw [Finset.sum_disjSum,←Nat.cast_smul_eq_nsmul ℂ,Poly.part_smul]
  simp [physical,row,Poly.inject,Poly.part]

theorem original (x:Grade (J) r)(unit:row x ∅=1):
    Equation (row x) (row (connected x)):=by
  let D:Derivation ℂ (Grade (J) r) (Grade (J) r):=euler (physical r)
  have whole:(Join.projectRight (J) (indices r)) x=1:=unit
  have coin:=congrArg (fun z:Poly (indices r)=>z.part (indices r).quiet) whole
  rw [Join.rprojection_quiet,Poly.one_part,if_pos rfl] at coin
  have neutral:(row (connected x)) ∅=0:=by
    change Join.projectRight (J) (indices r) (connected x)=0
    rw [Comparison.RG02.connected_maps _ (Join.rprojection_quiet (J) (indices r)) coin,whole]
    apply pass_inj (connected_quiet (by simp)) rfl
    rw [pass_connected (by simp),pass_zero]
  refine ⟨unit,neutral,?_⟩
  have h:=WilsonReceivedDepositedOrbitalEuler.pass D (connected x) (connected_quiet coin)
  rw [pass_connected coin] at h
  rw [←graded,←graded,←WilsonReceivedDepositedOrbitalColumns.product]
  exact congrArg row h

end YM.Integration.WilsonReceivedDepositedOrbitalEquation
end
