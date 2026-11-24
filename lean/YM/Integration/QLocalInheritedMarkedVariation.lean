import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Sails
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Rhyme

/-! A signed regular occurrence of the actual physical representation,
    enrolled at its reserved address with the original support and mask.
    The full colored forest computes its genuine pushed numerator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalInheritedMarkedVariation
open Function Filter Set Lattice RG Tree Wilson Pressure MeasureTheory
open PhysicalNext PhysicalNext.Repeat Progress.DirectedRecipe
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze ConnectedActivityE6.Matter
open ConnectedActivityE6.Blaze.March Precision Push.SectorMeasure
open Greenbelt Lotus Daisy Charity
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
    {P : Teller G} {L : Side} {x μ W α : ℝ} {Q : Target G P} {o : Target.Order G W}

def leaf (R : Rep G f) (z : RegularAddress f) (F : Config G f → ℝ) {u : ℝ}
    (regular : R.p.Regular z.support F) (bound : R.p.supBounds z.site z.support F u)
    (slots : HasSlots R.p R.activities) : Lotus.Leaf R := by
  let i := Blush.found z.site z.support z.anchor
  have addr : R.activities.reg i = z := Blush.latch R z.site z.support z.anchor slots
  refine ⟨.logKey i,masked R.p.threshold z.support F,?_,?_,slots.regular _,u,?_,?_,
    masked_measurable _ _ _ regular.borel⟩
  · change UsesFinal _ (R.activities.reg i).support _
    rw [addr]
    intro U V agree flags_eq
    have healthy : Healthy R.p.threshold z.support U ↔ Healthy R.p.threshold z.support V := by
      unfold Healthy
      rw [Finset.disjoint_iff_inter_eq_empty,flags_eq,Finset.disjoint_iff_inter_eq_empty]
    by_cases h : Healthy R.p.threshold z.support U
    · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ (healthy.mp h),regular.sites U V agree]
    · rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ (mt healthy.mpr h)]
  · change ∀ U, _ ≠ 0 → Healthy R.p.threshold (R.activities.reg i).support U
    rw [addr]
    intro U value
    exact of_not_not fun bad => value (masked_ne _ _ _ _ bad)
  · intro U
    by_cases h : Healthy R.p.threshold z.support U
    · rw [masked_eq _ _ _ _ h]
      exact bound.2 U h [] (by simp) (by simp)
    · rw [masked_ne _ _ _ _ h,norm_zero]
      exact bound.1
  · intro g U
    have healthy : Healthy R.p.threshold z.support (gauge g U) ↔ Healthy R.p.threshold z.support U := by
      unfold Healthy
      rw [gauge_flags]
    by_cases h : Healthy R.p.threshold z.support U
    · rw [masked_eq _ _ _ _ (healthy.mpr h),masked_eq _ _ _ _ h,regular.symmetry g U]
    · rw [masked_ne _ _ _ _ (mt healthy.mp h),masked_ne _ _ _ _ h]

variable {R : Rep G f} (z : RegularAddress f) (F : Config G f → ℝ) {u : ℝ}
  (reg : R.p.Regular z.support F) (bill : R.p.supBounds z.site z.support F u)
  (slots : HasSlots R.p R.activities)
local notation "M₀" => leaf R z F reg bill slots

theorem density (U : Config G f) :
    (M₀).cicada U = R.eval U * masked R.p.threshold z.support F U :=
  Blush.cliff (R:=R) (s:=Blush.found z.site z.support z.anchor) (U:=U) (t:=M₀) rfl

variable (H : Cash W x μ L Q o α T R) (χ : Chi) (V : Config G c) (t : ℝ) (a : Forest S.ratio)

theorem signed :
    HasSum (fun p => overhead (prism T x χ o.K V a) R Q.table *
      H.festo V (color (M₀) H χ V (-t)) p)
      (S.push R.beta R.eval V - t*S.push R.beta
        (fun U => R.eval U * masked R.p.threshold z.support F U) V) := by
  have eqn : (M₀).cicada = fun U => R.eval U * masked R.p.threshold z.support F U :=
    funext (density z F reg bill slots)
  simpa only [eqn,neg_mul,sub_eq_add_neg] using Charity.tint (M₀) H χ V (-t) a

private theorem divide_sum {ι : Type*} {u : ι → ℝ} {d t v : ℝ}
    (hd : 0 < d) (h : HasSum u (d-t*v)) :
    HasSum (fun i => d⁻¹ * u i) (1-t*(v/d)) := by
  have eqn : d⁻¹*(d-t*v) = 1-t*(v/d) := by field_simp [hd.ne']
  exact eqn ▸ h.mul_left d⁻¹

theorem normalized (positive : 0 < S.push R.beta R.eval V) :
    HasSum (fun p => (S.push R.beta R.eval V)⁻¹ *
      (overhead (prism T x χ o.K V a) R Q.table * H.festo V (color (M₀) H χ V (-t)) p))
      (1 - t * (S.push R.beta (fun U => R.eval U * masked R.p.threshold z.support F U) V /
        S.push R.beta R.eval V)) :=
  divide_sum positive (signed z F reg bill slots H χ V t a)

/-- One incoming envelope supplies the entire original sequence, each
    with an exact signed enrolled field at its own observed address. -/
theorem original (H : Cash W x μ L Q o α T R) (slots : HasSlots R.p R.activities) :
    ∃ u : ℕ → ℝ, (∀ i, R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support
      (R.activities.E i) (u i)) ∧ ∀ i, ∃ M : Lotus.Leaf R,
        M.turn = .logKey (Blush.found (R.activities.reg i).site (R.activities.reg i).support
          (R.activities.reg i).anchor) ∧ M.weight = u i ∧
        (∀ U, M.cicada U = R.eval U * R.activities.regularOccurrence R.p i U) ∧
        ∀ χ V t a, HasSum (fun p => overhead (prism T x χ o.K V a) R Q.table *
          H.festo V (color M H χ V (-t)) p)
          (S.push R.beta R.eval V - t*S.push R.beta
            (fun U => R.eval U * R.activities.regularOccurrence R.p i U) V) := by
  obtain ⟨u,hu,_⟩ := H.laws.intake.cap.labels.boundE
  refine ⟨u,hu,fun i => ?_⟩
  let z := R.activities.reg i
  let F := R.activities.E i
  have h := H.laws.intake.cap.labels.regular.smooth i
  exact ⟨leaf R z F h (hu i) slots,rfl,rfl,density z F h (hu i) slots,
    signed z F h (hu i) slots H⟩

end YM.Integration.QLocalInheritedMarkedVariation
end
