import YM.Integration.WilsonPositionProgramPublicDecoder
import YM.Integration.WilsonPositionProgramPublicCorrection

/-! Keep one measured decoder while the two finite submitted matrices vary.
Their numerical discrepancy is assessed before taking any limits. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicPerturbation
open Function Filter WilsonPositionProgramPublicCorrection
open scoped Classical Topology
variable {E P U : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P] {f : Filter U}

omit [FiniteDimensional ℂ P] in
theorem acquired (L : P →L[ℂ] E) (T : E →ₗ[ℂ] P) (exactly : ∀ v, L (T v) = v)
    (A : U → E →ₗ[ℂ] P)
    (comes : Tendsto (fun z => (A z).toContinuousLinearMap) f (𝓝 T.toContinuousLinearMap)) :
    ∀ᶠ z in f, Nonempty (Receipt (L.toLinearMap.comp (A z)) 2) := by
  let tol := (2*(1+‖L‖))⁻¹
  have pos : 0 < tol := by dsimp [tol];positivity
  have absorbed : ‖L‖ * tol ≤ 1/2 := by
    have roof : ‖L‖ ≤ 1+‖L‖ := by linarith
    calc
      _ ≤ (1+‖L‖)*tol := mul_le_mul_of_nonneg_right roof pos.le
      _ = _ := by dsimp [tol];field_simp
  filter_upwards [Metric.tendsto_nhds.mp comes tol pos] with z near
  apply integral
  intro x
  let D := (A z).toContinuousLinearMap - T.toContinuousLinearMap
  have normD : ‖D‖ ≤ tol := by simpa only [dist_eq_norm] using near.le
  have gap : L (A z x) - x = L (D x) := by
    change _ = L (A z x - T x)
    rw [map_sub,exactly]
  change ‖L (A z x)-x‖ ≤ _
  rw [gap]
  calc
    _ ≤ ‖L‖*‖D x‖ := L.le_opNorm _
    _ ≤ ‖L‖*(tol*‖x‖) := mul_le_mul_of_nonneg_left
      ((D.le_opNorm x).trans (mul_le_mul_of_nonneg_right normD (norm_nonneg _))) (norm_nonneg _)
    _ ≤ _ := by rw [← mul_assoc];exact mul_le_mul_of_nonneg_right absorbed (norm_nonneg _)

omit [FiniteDimensional ℂ E] in
theorem alignment (L : P →L[ℂ] E) (w s : E →ₗ[ℂ] P)
    (W : Receipt (L.toLinearMap.comp w) 2) (S : Receipt (L.toLinearMap.comp s) 2) :
    let V := W.change.trans S.change.symm
    (∀ x, L (s (V x)) = L (w x)) ∧
    (∀ x, ‖V x-x‖ ≤ 2*‖L‖*‖w x-s x‖) ∧
    (∀ x, w x=s x → V x=x) := by
  let V := W.change.trans S.change.symm
  have first (x : E) : W.change x = L (w x) := LinearMap.congr_fun W.reads x
  have output (x : E) : V x = S.change.symm (L (w x)) := congrArg S.change.symm (first x)
  constructor
  · intro x
    change L (s (V x))=_
    rw [output]
    exact (compare L.toLinearMap w s S (by norm_num) x).1
  constructor
  · intro x
    change ‖V x-x‖ ≤ _
    rw [output]
    exact (compare L.toLinearMap w s S (by norm_num) x).2.1
  · intro x eq
    change V x=x
    rw [output]
    exact (compare L.toLinearMap w s S (by norm_num) x).2.2 eq

end YM.Integration.WilsonPositionProgramPublicPerturbation
