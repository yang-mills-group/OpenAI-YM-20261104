import YM.Integration.WilsonThermometerRegisteredHistoryMass
import YM.Integration.WilsonFullFaceTestedSum

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSupportedCells
open Finset MeasureTheory Lattice Wilson RG PhysicalNext.Repeat.Legato Cells RG12 XSpace
open WilsonThermometerAlignedCells
open scoped Classical BigOperators

theorem restricted {α M:Type*} [Fintype α] [AddCommMonoid M] (p:α → Prop) [DecidablePred p]
    (f:α → M) (blank:∀x,¬p x → f x=0) :
    (∑x:{j // p j},f x.val)=∑x,f x :=by
  classical
  have h:(∑x:{j // ¬p j},f x.val)=0:=sum_eq_zero fun x _=>blank x.val x.property
  simpa only [h,add_zero] using Fintype.sum_subtype_add_sum_subtype p f

variable {G:Gauge} (R:Run G) {N per:ℕ} (r:ℝ) (profile:Test 3)
local notation "T" => Site (R.family.side N per)
abbrev Occupied := {y:T×T // mass (R:=R) r (N,per) profile y≠0}

theorem variation : (∑c:Occupied (N:=N) (per:=per) R r profile,‖mass (R:=R) r (N,per) profile c.val‖) ≤
    ∫x:Points 3,‖profile x‖ :=by
  classical
  rw [restricted _ (fun y=>‖mass (R:=R) r (N,per) profile y‖) (fun x h=>by simp [not_not.mp h])]
  exact WilsonThermometerAlignedCells.variation r (N,per) profile
end YM.Integration.WilsonThermometerSupportedCells
