import YM.Integration.WilsonPhysicalHistoryRetainedSpringAtomMoment
import YM.Integration.WilsonPhysicalHistoryRetainedSpringMean

/-! The actual countable list of occupied curvature paths retains its own
sum budget in every finite Gaussian moment. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Lattice RG Wilson Finset MeasureTheory WilsonMeasuredPathTaylor FundedCurvatureRayTaylor
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem row_moment (μ : Measure Ω) (v : Ω→Directions G n) (hv : Measurable v)
    (A : ℕ→Atom G k) {σ C M : ℝ} (hs : 0<σ) (pos : 0<M)
    (paid : SumBudget (fun i=>(A i).budget σ) C) (x : Site n) (q l : ℕ) (t : ℝ)
    (measured : ∀ e,AEStronglyMeasurable (fun z=>speed (v z) e) μ)
    (thermal : ∀ e,Integrable (fun z=>speed (v z) e^((q+1)*(l+1))) μ ∧
      (∫ z,speed (v z) e^((q+1)*(l+1)) ∂μ)≤M^((q+1)*(l+1))) :
    let d:=fun z=>(∑' i,((A i).unmasked (field (v z) t) x:ℂ))-
      ∑' i,polynomial (A i) x (v z) q t
    Integrable (fun z=>‖d z‖^(l+1)) μ ∧
      (∫ z,‖d z‖^(l+1) ∂μ)≤(C*(2*M*|t| /σ)^(q+1))^(l+1) := by
  intro d
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
  have visit (i : ℕ) (z : Ω) : Available (A i) x (v z) (B z) := fun _ e _=>
    single_le_sum (fun i _=>norm_nonneg (G.colorMat (v z i))) (mem_univ e)
  have each (z : Ω) (i : ℕ) : ‖E i z‖≤(A i).budget σ*K z :=
    (FundedCurvatureRayTaylor.original _ _ _ (b0 z) (visit i z) q t).trans
      (length_taylor (A i) hs (b0 z) q t)
  have rangeSum (z : Ω) : Summable (fun i=>‖E i z‖) :=
    Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (each z) (paid.2.1.mul_right _)
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
  have income (i : ℕ):=atom_moment μ v (A i) x q l t pos hs
    (fun _ e _=>measured e) (fun _ e _=>thermal e) (em i).aestronglyMeasurable
  have prices:=pool_series μ (fun i=>(A i).budget σ*c) (fun i z=>‖E i z‖) (paid.2.1.mul_right _)
    (fun i=>mul_nonneg (by unfold Atom.budget Atom.magnitude; positivity) c0)
    (fun _ _=>norm_nonneg _) (fun i=>(em i).norm) rangeSum l income
  have measurable : Measurable d:=by
    change Measurable (fun z=>(∑' i,u i z)-(∑' i,p i z))
    simp_rw [heq]
    exact Measurable.tsum em
  have bound (z : Ω) : ‖d z‖^(l+1)≤(∑' i,‖E i z‖)^(l+1):=by
    change ‖(∑' i,u i z)-(∑' i,p i z)‖^(l+1)≤_
    rw [heq]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_tsum_le_tsum_norm (rangeSum z)) _
  have hi:=prices.1.mono' (measurable.norm.pow_const _).aestronglyMeasurable (ae_of_all _ fun z=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]; exact bound z)
  refine ⟨hi,(integral_mono hi prices.1 bound).trans (prices.2.trans ?_)⟩
  rw [tsum_mul_right]
  apply pow_le_pow_left₀ (mul_nonneg (tsum_nonneg fun i=>by unfold Atom.budget Atom.magnitude; positivity) c0)
  exact mul_le_mul_of_nonneg_right paid.2.2 c0

end YM.Integration.OriginalMarkedRunAction
