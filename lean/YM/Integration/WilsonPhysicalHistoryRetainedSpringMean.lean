import YM.Integration.WilsonPhysicalHistoryRetainedSpringIntegral
import YM.Integration.WilsonPhysicalHistoryRetainedSpringJet

/-! The L¹ remainder of the full commissioned series. A torus-wide finite
moment is used only for integrability. Its cardinality cancels from the estimate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Lattice RG Wilson Finset MeasureTheory WilsonMeasuredPathTaylor FundedCurvatureRayTaylor
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem measured_row (μ : Measure Ω) (v : Ω→Directions G n) (hv : Measurable v)
    (A : ℕ→Atom G k) {σ C M : ℝ} (hs : 0<σ) (pos : 0<M)
    (paid : SumBudget (fun i=>(A i).budget σ) C) (x : Site n) (q : ℕ) (t : ℝ)
    (measured : ∀ e,AEStronglyMeasurable (fun z=>speed (v z) e) μ)
    (thermal : ∀ e,Integrable (fun z=>speed (v z) e^(q+1)) μ ∧
      (∫ z,speed (v z) e^(q+1) ∂μ)≤M^(q+1)) :
    let d:=fun z=>(∑' i,((A i).unmasked (field (v z) t) x:ℂ))-
      ∑' i,polynomial (A i) x (v z) q t
    Integrable d μ ∧ (∫ z,‖d z‖ ∂μ)≤C*(2*M*|t|/σ)^(q+1) := by
  let u (i : ℕ) (z : Ω) : ℂ:=(A i).unmasked (field (v z) t) x
  let p (i : ℕ) (z : Ω):=polynomial (A i) x (v z) q t
  let E (i : ℕ) (z : Ω):=u i z-p i z
  let B (z : Ω):=∑ e : Edge (Site n),speed (v z) e
  let K (z : Ω):=(2*B z*|t|/σ)^(q+1)
  let c:=(2*M*|t|/σ)^(q+1)
  have c0 : 0≤c:=by dsimp only [c]; positivity
  have b0 (z : Ω) : 0≤B z:=sum_nonneg fun _ _=>norm_nonneg _
  have fieldM : Measurable (fun z=>field (v z) t) := measurable_pi_iff.mpr fun e=>
    G.lieExp_cont.measurable.comp (((measurable_pi_apply e).comp hv).const_smul t)
  have em (i : ℕ) : Measurable (E i) :=
    (Complex.continuous_ofReal.measurable.comp (((A i).unmasked_cont x).measurable.comp fieldM)).sub
      ((polynomial_continuous (A i) x q t).measurable.comp hv)
  have receipt i:=measured_atom_error μ v (A i) x q t pos hs
    (fun _ e _=>measured e) (fun _ e _=>thermal e) (em i).aestronglyMeasurable
  have visit (i : ℕ) (z : Ω) : Available (A i) x (v z) (B z) := fun _ e _=>
    single_le_sum (fun i _=>norm_nonneg (G.colorMat (v z i))) (mem_univ e)
  have each (z : Ω) (i : ℕ) : ‖E i z‖≤(A i).budget σ*K z :=
    (FundedCurvatureRayTaylor.original _ _ _ (b0 z) (visit i z) q t).trans
      (length_taylor (A i) hs (b0 z) q t)
  have rangeSum (z : Ω) : Summable (fun i=>‖E i z‖) :=
    Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (each z) (paid.2.1.mul_right _)
  have point (z : Ω) : (∑' i,‖E i z‖)≤C*K z := by
    apply ((rangeSum z).tsum_le_tsum (each z) (paid.2.1.mul_right _)).trans
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right paid.2.2 (pow_nonneg (div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (b0 z)) (abs_nonneg t)) hs.le) _)
  have wholeScore:=QLocalMeasuredPathMoments.pooled μ univ (fun _ : Edge (Site n)=>M)
    (fun e z=>speed (v z) e) (fun _ _=>pos) (fun e _ z=>norm_nonneg (G.colorMat (v z e)))
    (fun e _=>measured e) q (fun e _=>thermal e)
  have ik : Integrable K μ := by
    have eq (z : Ω) : K z=(B z)^(q+1)*(2*|t|/σ)^(q+1) := by
      dsimp only [K]; rw [←mul_pow]; apply congrArg (fun x : ℝ=>x^(q+1)); ring
    simp_rw [show K=fun z=>(B z)^(q+1)*(2*|t|/σ)^(q+1) from funext eq]
    exact wholeScore.1.mul_const _
  have absInt : Integrable (fun z=>∑' i,‖E i z‖) μ :=
    (ik.const_mul C).mono' (Measurable.tsum fun i=>(em i).norm).aestronglyMeasurable
      (ae_of_all _ fun z=>(Real.norm_of_nonneg (tsum_nonneg fun i=>norm_nonneg (E i z))).le.trans (point z))
  have dom (z : Ω) := norm_tsum_le_tsum_norm (rangeSum z)
  have actual := absInt.mono' (Measurable.tsum em).aestronglyMeasurable (ae_of_all μ dom)
  have hu (z : Ω) : Summable (fun i=>u i z) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ (paid.2.1.mul_right (2^k))
    intro i
    change ‖((A i).unmasked (field (v z) t) x:ℂ)‖≤_
    rw [Complex.norm_real]
    exact ((A i).unmasked_bound _ _).trans
      (mul_le_mul_of_nonneg_right ((A i).lower_budget σ hs) (by positivity))
  have heq z : (∑' i,u i z)-(∑' i,p i z)=∑' i,E i z := by
    have pp : Summable (fun i=>p i z) := by
      simpa only [E,Pi.sub_apply,sub_sub_cancel] using (hu z).sub (rangeSum z).of_norm
    exact ((hu z).tsum_sub pp).symm
  dsimp only
  change Integrable (fun z=>(∑' i,u i z)-(∑' i,p i z)) μ ∧ _≤_
  simp_rw [show (fun z=>(∑' i,u i z)-(∑' i,p i z))=(fun z=>∑' i,E i z) from funext heq]
  refine ⟨actual,?_⟩
  change (∫ z,‖(∑' i,u i z)-(∑' i,p i z)‖ ∂μ)≤_
  simp_rw [heq]
  have prices : Summable (fun i=>∫ z,‖E i z‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun _=>integral_nonneg (fun _=>norm_nonneg _))
      (fun i=>(receipt i).2) (paid.2.1.mul_right c)
  apply (integral_mono actual.norm absInt dom).trans
  rw [←integral_tsum_of_summable_integral_norm (fun i=>(receipt i).1.norm)
    (by simpa only [Real.norm_eq_abs,abs_norm] using prices)]
  apply (prices.tsum_le_tsum (fun i=>(receipt i).2) (paid.2.1.mul_right _)).trans
  rw [tsum_mul_right]
  exact mul_le_mul_of_nonneg_right paid.2.2 c0

end YM.Integration.OriginalMarkedRunAction
