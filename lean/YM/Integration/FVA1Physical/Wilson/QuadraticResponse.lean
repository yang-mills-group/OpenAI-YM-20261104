import YM.Integration.FVA1Physical.Wilson.QuadraticTaylor

/-! Complex physical responses can be recharted on affine clouds and priced
as actual finite polynomials, without any loss proportional to the torus. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson.SignCovariance
open Function Filter Finset MeasureTheory Matrix Push.Uniform Comparison.RG02 Valence
open YM.Next.SectorChange YM.Analysis
open scoped BigOperators Classical ContDiff Topology

variable {E X Y Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem affine_degree (z:Y) (L:X→L[ℝ]Y) {n:ℕ} {f:Y→Z}
    (hf:Level (n:ℤ) f) : Level (n:ℤ) (fun x=>f (z+L x)) := by
  induction n generalizing f with
  | zero =>
    have con : (fun x=>f (z+L x)) = fun _=>f 0 := funext fun x=>by
      simpa [Assembly.jet_zero] using hf.posted (z+L x)
    rw [con]; exact Level.constant _
  | succ n ih =>
    apply Level.up (by positivity) (hf.smooth.comp (contDiff_const.add L.contDiff))
    intro v
    have hd : D v (fun x=>f (z+L x))=fun x=>D (L v) f (z+L x) := by
      funext x
      have der : HasFDerivAt (fun u=>f (z+L u)) ((fderiv ℝ f (z+L x)).comp L) x :=
        (hf.smooth.contDiffAt.differentiableAt (by simp)).hasFDerivAt.comp x (L.hasFDerivAt.const_add z)
      exact congrArg (fun T:X→L[ℝ]Z=>T v) der.fderiv
    change Level _ (D v (fun x=>f (z+L x)))
    rw [hd,show ((n+1:ℕ):ℤ)-1=(n:ℤ) by omega]
    apply ih
    convert hf.down (L v) using 1; omega

theorem projected_degree {n:ℤ} {f:E→Y} (h:Level n f) (l:Y→L[ℝ]Z) : Level n (l ∘ f) := by
  refine ⟨l.contDiff.comp h.smooth,fun i hi x=>?_⟩
  rw [l.iteratedFDeriv_comp_left h.smooth.contDiffAt le_top,h.high i hi x]
  ext v;exact l.map_zero

variable {ι:Type} [Fintype ι] [DecidableEq ι]
theorem complex_quadratic_expectation (f:(ι→ℝ)→ℂ) (degree:Level 2 f) (K:Matrix ι ι ℝ)
    (pd:K.PosDef) {a C δ:ℝ} (ha:0<a) (hc:0≤C) (rows:∀i,∑ j,|K i j|≤C)
    (cube:∀z,‖z‖≤a→‖f z‖≤δ) :
    ‖∫ z, f z ∂Gaussian.cloud K‖ ≤ 2*(δ + 4*(1+C)*δ/a^2) := by
  by_cases hf : Integrable f (Gaussian.cloud K)
  · have re := level_two_expectation (Complex.reCLM ∘ f) (projected_degree degree _) K pd ha hc rows
      (fun z hz=>(Complex.abs_re_le_norm _).trans (cube z hz))
    have im := level_two_expectation (Complex.imCLM ∘ f) (projected_degree degree _) K pd ha hc rows
      (fun z hz=>(Complex.abs_im_le_norm _).trans (cube z hz))
    change |∫ z,Complex.reCLM (f z) ∂Gaussian.cloud K| ≤ _ at re
    rw [Complex.reCLM.integral_comp_comm hf] at re
    change |∫ z,Complex.imCLM (f z) ∂Gaussian.cloud K| ≤ _ at im
    rw [Complex.imCLM.integral_comp_comm hf] at im
    exact (Complex.norm_le_abs_re_add_abs_im _).trans ((add_le_add re im).trans_eq (by ring))
  · have hδ : 0≤δ := (norm_nonneg (f 0)).trans (cube 0 (by simpa using ha.le))
    rw [integral_undef hf,norm_zero];positivity
end YM.Integration.FVA1Physical.Wilson.SignCovariance
