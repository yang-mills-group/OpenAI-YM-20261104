import YM.Integration.WilsonNeutralNominatedFiniteTable

/-! Real submissions on the same Wilson law recover the full complex moments
of the three named fields on every mask. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonNeutralNominatedScalarFaces
open Lattice Wilson Source MeasureTheory PhysicalNext.Repeat.Legato Finset
open WilsonNeutralOffsetCutoff WilsonPositionThermometerCapStation
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G)

def phase (imag : Finset (Fin 3)) (i : Fin 3) : ℂ →ₗ[ℝ] ℝ :=
  if i ∈ imag then Complex.imCLM.toLinearMap else Complex.reCLM.toLinearMap

private theorem expand (q : Fin 3 → ℂ) (S : Finset (Fin 3)) :
    ∏ i ∈ S, q i = ∑ J ∈ S.powerset, Complex.I ^ J.card *
      ∏ i ∈ S, ((phase J i (q i) : ℝ) : ℂ) := by
  calc ∏ i ∈ S, q i = ∏ i ∈ S, (((q i).im : ℂ)*Complex.I + (q i).re) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [add_comm, Complex.re_add_im]
    _ = _ := by
      rw [Finset.prod_add]
      apply Finset.sum_congr rfl
      intro J sub
      have h := Finset.mem_powerset.mp sub
      have im : (∏ i ∈ J, ((phase J i (q i) : ℝ) : ℂ)) = ∏ i ∈ J, ((q i).im : ℂ) :=
        Finset.prod_congr rfl fun i hi => by simp [phase,hi]
      have re : (∏ i ∈ S \ J, ((phase J i (q i) : ℝ) : ℂ)) = ∏ i ∈ S \ J, ((q i).re : ℂ) :=
        Finset.prod_congr rfl fun i hi => by simp [phase,(Finset.mem_sdiff.mp hi).2]
      rw [← Finset.prod_sdiff h (f:=fun i => ((phase J i (q i) : ℝ) : ℂ)),re,im,Finset.prod_mul_distrib,
        Finset.prod_const]
      ring

def factor (A : Group R.family 6) (N per : ℕ) (z : Fin 3 → Site (R.family.side N per))
    (S J : Finset (Fin 3)) (U : Config G (R.family.side N per)) : ℂ :=
  ∏ i ∈ S, ((phase J i (R.family.O N per (named R A N per i) (z i) U) : ℝ) : ℂ)

/-- One original denominator is used for every fired component and every proper
face. The finite phases act on the very same full cutoff fields and sites. -/
theorem original (A : Group R.family 6) (N per : ℕ) (z : Fin 3 → Site (R.family.side N per))
    (S : Finset (Fin 3)) :
    R.family.omega N per (fun U => ∏ i ∈ S, R.family.O N per (named R A N per i) (z i) U) =
      ∑ J ∈ S.powerset, Complex.I ^ J.card * R.family.omega N per (factor R A N per z S J) := by
  let U := Config G (R.family.side N per)
  let μ := law G (R.family.side N per) (R.family.beta N per)
  have cont (J : Finset (Fin 3)) : Continuous (factor R A N per z S J) := by
    apply continuous_finsetProd
    intro i _
    have c := R.family.continuousO N per _ (named R A N per i) (z i)
    by_cases h : i ∈ J
    · simpa [phase,h,Function.comp_def] using Complex.continuous_ofReal.comp (Complex.continuous_im.comp c)
    · simpa [phase,h,Function.comp_def] using Complex.continuous_ofReal.comp (Complex.continuous_re.comp c)
  have pass : (fun W : U => ∏ i ∈ S, R.family.O N per (named R A N per i) (z i) W) =
      fun W => ∑ J ∈ S.powerset, Complex.I ^ J.card * factor R A N per z S J W :=
    funext fun W => expand _ S
  rw [pass]
  change (∫ W, ∑ J ∈ S.powerset, Complex.I ^ J.card * factor R A N per z S J W ∂μ) = _
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro J _
    exact integral_const_mul _ _
  · intro J _
    exact continuous_integrable _ (continuous_const.mul (cont J))

end YM.Integration.WilsonNeutralNominatedScalarFaces

