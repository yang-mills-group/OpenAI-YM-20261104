import YM.Integration.FVA1Physical.Wilson.SignCovariance
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.TotalCost

/-! The genuine finite Gaussian expectation of any quadratic perturbation,
priced from its deterministic sup-norm on the earned ball and the spatial
row charge of the chosen covariance, independently of the number of sites. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson.SignCovariance
open Function Matrix Finset MeasureTheory ProbabilityTheory Lattice AllOrder.Iron Push.Uniform
open YM.Next.SectorChange YM.AnalyticBridge.LocalGaussianLaws
open scoped BigOperators Classical

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem bilinear_symm (W:Matrix ι ι ℝ) (s:W.IsSymm) (x y:ι→ℝ) :
    bilinear W x y = bilinear W y x := by
  unfold bilinear
  rw [Finset.sum_comm]
  apply sum_congr rfl;intro i _
  apply sum_congr rfl;intro j _
  rw [s.apply j i];ring

omit [DecidableEq ι] in
private theorem polar (W:Matrix ι ι ℝ) (s:W.IsSymm) (x y:ι→ℝ) (a b:ℝ) :
    bilinear W (a • x+b • y) (a • x+b • y)-bilinear W (a • x-b • y) (a • x-b • y) =
        (4*a*b)*bilinear W x y := by
  calc _ = (2*a*b)*(bilinear W x y+bilinear W y x) := by
          unfold bilinear
          simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,←Finset.sum_sub_distrib,
            ←Finset.sum_add_distrib,Finset.mul_sum]
          apply sum_congr rfl;intro i _
          apply sum_congr rfl;intro j _;ring
       _ = _ := by rw [bilinear_symm W s y x];ring

theorem cube_contraction (W K:Matrix ι ι ℝ) (s:W.IsSymm) {A C δ:ℝ}
    (hA:0<A) (hC:0≤C) (rows:∀ i,∑ j,|K i j|≤C)
    (cube:∀ z:ι→ℝ, ‖z‖≤A → |bilinear W z z|≤δ) :
    |∑ i,∑ j,W i j*K j i| ≤ 2*(1+C)*δ/A^2 := by
  apply contraction W K hC rows
  intro u v hu hv
  let a:=A/2
  let b:=A/(2*(1+C))
  have ha : 0<a := by dsimp [a];positivity
  have hb : 0<b := by dsimp [b];positivity
  have ua:‖a • u‖ ≤ A/2 := by rw [norm_smul,Real.norm_of_nonneg ha.le];simpa [a] using mul_le_mul_of_nonneg_left hu ha.le
  have vb:‖b • v‖ ≤ A/2 := by
    rw [norm_smul,Real.norm_of_nonneg hb.le]
    calc b*‖v‖ ≤ b*(1+C) := mul_le_mul_of_nonneg_left (hv.trans (by linarith)) hb.le
         _ = _ := by dsimp [b];field_simp
  have x:=cube (a•u+b•v) ((norm_add_le ..).trans (by linarith only [ua,vb]))
  have y:=cube (a•u-b•v) ((norm_sub_le ..).trans (by linarith only [ua,vb]))
  have cmp : |bilinear W (a•u+b•v) (a•u+b•v) - bilinear W (a•u-b•v) (a•u-b•v)| ≤ δ+δ :=
    (abs_sub _ _).trans (add_le_add x y)
  rw [polar W s u v a b,abs_mul,abs_of_pos (show 0<4*a*b by positivity)] at cmp
  apply (le_div_iff₀ (sq_pos_of_pos hA)).2
  have hz:=mul_le_mul_of_nonneg_right cmp (show 0≤1+C by linarith)
  have cost : (4*a*b)*(1+C)=A^2 := by dsimp [a,b];field_simp;ring
  calc |bilinear W u v| *A^2 = (4*a*b*|bilinear W u v|)*(1+C) := by rw [←cost];ring
       _ ≤ _ := hz.trans_eq (by ring)

private theorem gaussian_entry (K:Matrix ι ι ℝ) (pd:K.PosDef) (i j:ι) :
    (∫ z:ι→ℝ,z i*z j ∂Gaussian.cloud K) = K i j := by
  simpa only [ProbabilityTheory.covariance,Gaussian.cloud_center,sub_zero] using Gaussian.cloud_cov K pd i j

theorem quadratic_gaussian (W K:Matrix ι ι ℝ) (pd:K.PosDef) :
    (∫ z:ι→ℝ,bilinear W z z ∂Gaussian.cloud K) = ∑ i,∑ j,W i j*K j i := by
  let μ:=Gaussian.cloud K
  have integ (i j:ι) : Integrable (fun z:ι→ℝ=>W i j*z i*z j) μ := by
    simp_rw [mul_assoc]
    exact ((Density.first_debit K i).integrable_mul (Density.first_debit K j)).const_mul _
  unfold bilinear
  rw [integral_finsetSum _ (fun i _=>integrable_finsetSum _ fun j _=>integ i j)]
  apply sum_congr rfl;intro i _
  rw [integral_finsetSum _ (fun j _=>integ i j)]
  apply sum_congr rfl;intro j _
  simp only [mul_assoc,integral_const_mul]
  exact congrArg (fun y:ℝ=>W i j*y) ((gaussian_entry K pd i j).trans ((Matrix.isHermitian_iff_isSymm.mp pd.isHermitian).apply j i))

theorem gaussian_cube_price {n:Side} {loc:ι→Site n} {η C A δ:ℝ} {k:ℕ} (W K:Matrix ι ι ℝ)
    (pd:K.PosDef) (sym:W.IsSymm) (hη:0<η) (hc:0≤C) (mult:Multiplicity loc k)
    (cap:Capped n loc loc η C K) (ha:0<A)
    (small:∀ z:ι→ℝ,‖z‖≤A→|bilinear W z z|≤δ) :
    |∫ z:ι→ℝ,bilinear W z z ∂Gaussian.cloud K| ≤ 2*(1+C*metric η k)*δ/A^2 := by
  rw [quadratic_gaussian W K pd]
  apply cube_contraction W K sym ha _ (capped_row K hc hη cap mult) small
  exact mul_nonneg hc (mul_nonneg (Nat.cast_nonneg _) (count_pos hη).le)

end YM.Integration.FVA1Physical.Wilson.SignCovariance
