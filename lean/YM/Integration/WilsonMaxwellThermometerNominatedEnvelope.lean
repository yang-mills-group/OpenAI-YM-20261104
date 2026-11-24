import YM.Euclid.Test
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Separation.Regular

/-! A single real nonnegative smooth wallet on the same separated chart
dominates the absolute value of the genuine signed compact profile. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedEnvelope
open Set Function Filter MeasureTheory
open scoped Classical Topology
theorem original {n:ℕ} (φ:Test n):∃ψ:Test n,∀x:Points n,
    ψ x=(‖ψ x‖:ℂ) ∧ ‖φ x‖≤‖ψ x‖:=by
  let K:=tsupport (fun x=>φ x)
  obtain ⟨U,uo,ku,legal,compact⟩:=exists_open_between_and_isCompact_closure φ.hasCompactSupport (conf_open n) φ.tsupport_subset
  obtain ⟨f,supp,smooth,range⟩:=uo.exists_contDiff_support_eq (n:=⊤)
  have hpos (x:Points n):0≤f x:=(range ⟨x,rfl⟩).1
  have hnz (x:Points n) (hx:x∈K):f x≠0:=by
    have u:=ku hx
    rw [←supp] at u
    exact u
  have c:ContinuousOn (fun x:Points n=>‖φ x‖/(f x)) K:=
    φ.continuous.norm.continuousOn.div smooth.continuous.continuousOn hnz
  obtain ⟨b,hb⟩:=(φ.hasCompactSupport.image_of_continuousOn c).bddAbove
  let C:=max 1 b
  have cp:0<C:=lt_of_lt_of_le zero_lt_one (le_max_left ..)
  let ζ:Points n→ℂ:=fun x=>(C*f x:ℝ)
  have keep:tsupport ζ⊆closure U:=by
    refine closure_mono fun x non=>?_
    rw [←supp]
    intro h
    exact non (by simp [ζ,h])
  let ψ:Test n:=⟨ζ,Complex.ofRealCLM.contDiff.comp (contDiff_const.mul smooth),
    compact.of_isClosed_subset isClosed_closure keep,keep.trans legal⟩
  refine ⟨ψ,?_⟩
  intro x
  have eq:‖ψ x‖=C*f x:=by change ‖((C*f x:ℝ):ℂ)‖=_; rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg cp.le (hpos x))]
  refine ⟨by rw [eq];rfl,?_⟩
  rw [eq]
  by_cases hx:x∈K
  · have m:=hb ⟨x,hx,rfl⟩
    exact (div_le_iff₀ (lt_of_le_of_ne (hpos x) (hnz x hx).symm)).mp (m.trans (le_max_right ..))
  · have zero:φ x=0:=by
      by_contra non
      exact hx (subset_tsupport (fun y=>φ y) non)
    rw [zero,norm_zero]
    exact mul_nonneg cp.le (hpos x)

end YM.Integration.WilsonMaxwellThermometerNominatedEnvelope
