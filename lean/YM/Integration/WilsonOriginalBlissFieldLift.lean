import YM.Integration.WilsonOriginalBlissObserved

/-! Lift an actual requested continuum field into its original cutoff chart.
The measured forward arch and the engineering factor use the same date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalBlissFieldLift
open Filter Lattice Wilson RG Extraction Extraction.Banks Spec Table RG17
open scoped Classical Topology
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
  (F:Spec.Final C f S){H:(Climb.Bel C.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}
  (arch:Trace.Terrace.Arch C)(bliss:Trace.Pilot.Bliss F l arch H)
  (J:ℝ→PhysMS.tower S)(level:ℝ→ℕ)
  (shift:∀ d,ℝ→C.label d ≃ₗ[ℂ] C.label d)
local notation "L"=>WilsonOriginalBlissObserved.layout F bliss J level shift

def column (d:ℕ)(r:ℝ):S.Field d →ₗ[ℂ] C.label d :=
  (shift d r).symm.toLinearMap.comp ((arch.M d (level r)).toLinearMap.comp
    ((((C.S.a (level r)^d:ℝ):ℂ)⁻¹) • S.representative d))

private theorem engineering (d:ℕ)(r:ℝ):((C.S.a (level r)^d:ℝ):ℂ) ≠ 0 := by
  exact_mod_cast (pow_pos (C.S.a_pos _) d).ne'

theorem located (d:ℕ)(r:ℝ)(x:S.Field d):
    locatedRef L d r (column arch level shift d r x) = S.representative d x := by
  change ((C.S.a (level r)^d:ℝ):ℂ) • (arch.M d (level r)).symm
    ((shift d r) ((shift d r).symm ((arch.M d (level r))
      (((C.S.a (level r)^d:ℝ):ℂ)⁻¹ • S.representative d x))))=_
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply,smul_smul,
    mul_inv_cancel₀ (engineering level d r),one_smul]

theorem field (d:ℕ)(r:ℝ)(x:S.Field d):
    RG17.master L d r (column arch level shift d r x)=x := by
  rw [←RG17.payRef,located,S.rep]

theorem measured (d:ℕ)(r:ℝ)(active:C.ref d≤level r):
    ∀ᶠ u:(ℕ×ℕ) in (l:Filter (ℕ×ℕ)),∀x:S.Field d,
      Trace.Terrace.Cturn C d (level r) u.1 u.2
        (atRef L d r u (column arch level shift d r x)) =
          arch.M d (level r) (S.representative d x) := by
  filter_upwards [WilsonOriginalBlissObserved.measured F bliss J level shift d r active] with u paid
  intro x
  rw [paid]
  change ((C.S.a (level r)^d:ℝ):ℂ) • (shift d r)
    ((shift d r).symm ((arch.M d (level r)) (((C.S.a (level r)^d:ℝ):ℂ)⁻¹ • S.representative d x)))=_
  rw [LinearEquiv.apply_symm_apply,map_smul,smul_smul,mul_inv_cancel₀ (engineering level d r),one_smul]

end YM.Integration.WilsonOriginalBlissFieldLift
