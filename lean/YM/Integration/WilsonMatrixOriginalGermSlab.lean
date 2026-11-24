import YM.Integration.WilsonMatrixOriginalGermReplica
import YM.Integration.WilsonReportingTopEnvelope
import YM.Integration.WilsonMatrixTicketLanesReportedAdmission

/-! An actual two-copy response can be priced from the original submitted
labels when the two lattice spacings remain comparable. The complete
signed mesh and both proper means are charged before the period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermSlab
open MeasureTheory Filter Lattice Wilson RG RG17 RG12 OPE.Therm PhysicalNext.Repeat.Legato Push.GridApprox FVA2
open WilsonMatrixOriginalGermGram WilsonMatrixOriginalGermTwoMarkJoint WilsonMatrixOriginalGermSignedPrior
open WilsonMatrixOriginalGermSpringHearing WilsonMatrixOriginalGermSpringPanel WilsonMatrixOriginalGermPanelRMS
open WilsonMatrixOriginalGermConditionalMask Extra.Multi.BasisCost
open scoped BigOperators Classical
open private tested from YM.Integration.WilsonMatrixOriginalGermMaskPanel
open private energy from YM.Integration.WilsonMatrixOriginalGermPanelRMS
variable {G:Gauge} (R:Run G) {m k N p:ℕ}
local notation "β" i => R.family.path.levels.clock.hatBeta i

private theorem centered_bound {X Y:Config G (R.family.side N p)→ℂ} {a b:ℝ}
    (ap:0≤a) (hx:∀U,‖X U‖≤a) (hy:∀U,‖Y U‖≤b) (U:Config G (R.family.side N p)):
    ‖centered R X Y U‖≤6*(a*b):=by
  let μ:=scene R.family.path N p N
  letI:IsProbabilityMeasure μ:=OPE.Therm.probability R.makes.wilson (le_refl N)
  have price {H:Config G (R.family.side N p)→ℂ} {c:ℝ} (h:∀T,‖H T‖≤c):‖∫T,H T ∂μ‖≤c:=
    by simpa using norm_integral_le_of_norm_le_const (μ:=μ) (Eventually.of_forall h)
  have px:=price hx
  have py:=price hy
  have joint:‖∫T,X T*Y T ∂μ‖≤a*b:=price (fun T=>by rw [norm_mul];exact mul_le_mul (hx T) (hy T) (norm_nonneg _) ap)
  have cov:‖moment μ X Y‖≤a*b+a*b:=by
    apply (norm_sub_le ..).trans
    rw [norm_mul]
    exact add_le_add joint (mul_le_mul px py (norm_nonneg _) ap)
  have x:‖X U-(∫T,X T ∂μ)‖ ≤ a+a:=(norm_sub_le ..).trans (add_le_add (hx U) px)
  have y:‖Y U-(∫T,Y T ∂μ)‖ ≤ b+b:=(norm_sub_le ..).trans (add_le_add (hy U) py)
  apply (norm_sub_le ..).trans
  rw [norm_mul]
  exact (add_le_add (mul_le_mul x y (norm_nonneg _) (add_nonneg ap ap)) cov).trans_eq (by ring)

private theorem conditional_bound (lower:m≤k) (upper:k≤N) (v:Fin 2→R.family.label 4) (φ:Test 2)
    {B:ℝ} (bp:0≤B) (h:∀U,‖panel R (p:=p) (lower.trans upper) v φ U‖≤B):cost R (p:=p) lower upper v φ≤B:=by
  let K:=WilsonMatrixOriginalGermReplica.history R.family N p N k upper
  letI:ProbabilityTheory.IsMarkovKernel K:=WilsonMatrixOriginalGermReplica.probability R.family N p N R.makes (le_refl N) upper
  let μ:=scene R.family.path N p k
  letI:IsProbabilityMeasure μ:=OPE.Therm.probability R.makes.wilson upper
  have bound (T):‖response R (p:=p) lower upper v φ T‖≤B:=by
    rw [response,←WilsonMatrixOriginalGermReplica.actual R.family N p N R.makes (le_refl N) (tested R _ v φ) upper T]
    simpa only [Measure.real_def,measure_univ,ENNReal.toReal_one,mul_one] using norm_integral_le_of_norm_le_const (μ:=K T) (Eventually.of_forall h)
  have paid:Integrable (fun U=>‖response R (p:=p) lower upper v φ U‖^2) μ:=
    energy μ (entered R lower upper v φ).1
  have limit:(∫U,‖response R (p:=p) lower upper v φ U‖^2 ∂μ)≤B^2:=by
    simpa using integral_mono paid (integrable_const (μ:=μ) (B^2)) (fun U=>pow_le_pow_left₀ (norm_nonneg _) (bound U) 2)
  exact (Real.sqrt_le_sqrt limit).trans_eq (Real.sqrt_sq bp)

/-- The upper price uses both true bare lattice fields at their enrolled
addresses and the absolute quadrature mass of the submitted signed test. -/
theorem capped (lower:m≤k) (upper:k≤N) (v:Fin 2→R.family.label 4) (φ:Test 2) (a:Fin 2→ℝ)
    (ap:∀i,0≤a i) (funded:∀i (o:Site (R.family.side N p)) U,‖R.family.O N p (v i) o U‖≤a i):
    cost R (p:=p) lower upper v φ ≤ (∑x:Fin 2→Site (R.family.side N p),‖WilsonExternalMeshMass.charge R.family φ x‖)*
      (6*(a 0*a 1)):=by
  let f:=fun x:Fin 2→Site (R.family.side N p)=>WilsonExternalMeshMass.charge R.family φ x
  have positive:0≤6*(a 0*a 1):=by positivity [ap 0,ap 1]
  apply conditional_bound R lower upper v φ (mul_nonneg (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) positive)
  intro U
  change ‖∑x,f x*centered R (source R (lower.trans upper) (v 0) x 0) (source R (lower.trans upper) (v 1) x 1) U‖≤_
  apply (norm_sum_le ..).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (centered_bound R (ap 0) (funded 0 _) (funded 1 _) U) (norm_nonneg _)

end YM.Integration.WilsonMatrixOriginalGermSlab
