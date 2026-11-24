import YM.SchemeConversionRG11.Maxwell.OrbitTest
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! # Laplacian trace on the real ball for Wick moment invariants

Constants unnormalized for volume. Does not use perturbative OPE. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter MeasureTheory Metric Maxwell Tensor Set MvPolynomial
open scoped Topology BigOperators RealInnerProductSpace

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

abbrev Bean (ι : Type) [Fintype ι] := EuclideanSpace ℝ ι
abbrev ShellBook (ι : Type) := MvPolynomial ι ℂ

def bat (i : ι) : Bean ι := EuclideanSpace.single i 1
lemma bat_norm (i : ι) : ‖bat i‖=1 := by simp [bat]

def laser (x : Bean ι) : ShellBook ι := ∑ i, (x i:ℂ) • X i
lemma laser_smul (t : ℝ) (x : Bean ι) : laser (t • x)= (t:ℂ) • laser x := by
  simp only [laser,PiLp.smul_apply,smul_eq_mul,Complex.ofReal_mul,Finset.smul_sum,smul_smul]
lemma laser_add (x y : Bean ι) : laser (x+y)=laser x+laser y := by
  simp only [laser,PiLp.add_apply,Complex.ofReal_add,add_smul,Finset.sum_add_distrib]
lemma laser_atom (i : ι) : laser (bat i)=X i := by simp [laser,bat,PiLp.single_apply]
lemma inner_lase (x y : Bean ι) : aeval (fun i ↦ (x i:ℂ)) (laser y)=(⟪x,y⟫:ℂ) := by
  simp only [laser,map_sum,map_smul,aeval_X,smul_eq_mul]
  rw [show ⟪x,y⟫=∑ i, y i*x i from rfl,Complex.ofReal_sum]; simp only [Complex.ofReal_mul]
lemma scorch (x : Bean ι) (i : ι) : pderiv i (laser x)=C (x i:ℂ) := by simp only [laser,map_sum,Derivation.map_smul]; rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _),pderiv_X_self,← C_mul',mul_one]; intro a _ h; rw [pderiv_X_of_ne h,smul_zero]
lemma laser_flip (x : Bean ι) : laser (-x) = - laser x := by rw [← neg_one_smul ℝ x,laser_smul]; simp

omit [DecidableEq ι] in
lemma burn (x : Bean ι) (n : ℕ) : hot ι ((laser x)^(n+2))=
    ((n+2:ℕ)*(↑(n+1:ℕ):ℂ)*(↑(‖x‖^2):ℂ)) • (laser x)^n := by
  classical
  have hw (j : ℕ) (i : ι) : pderiv i (laser x^(j+1))=( (↑(j+1:ℕ):ℂ)*(x i:ℂ)) • laser x^j := by
    rw [pderiv_pow,Nat.add_sub_cancel,scorch,← C_mul', map_mul (C (R:=ℂ)), map_natCast (C (R:=ℂ))]; ring
  have hs : (↑(‖x‖^2):ℂ)=∑ i, (x i:ℂ)*(x i:ℂ) := by
    rw [←real_inner_self_eq_norm_sq, show ⟪x,x⟫=∑ i,x i*x i from rfl,Complex.ofReal_sum]; simp only [Complex.ofReal_mul]
  rw [hot_read]; simp_rw [show n+2=n+1+1 from rfl,hw, Derivation.map_smul,hw, hs,Finset.mul_sum,Finset.sum_smul, smul_smul]
  apply Finset.sum_congr rfl; intro i _; congr 1
  ring

omit [DecidableEq ι] in
lemma burn_first (x : Bean ι) : hot ι (laser x)=0 := by classical rw [hot_read]; simp_rw [scorch,pderiv_C]; rw [Finset.sum_const_zero]

omit [DecidableEq ι] in
lemma burn_one : hot ι 1=0 := by classical rw [hot_read]; simp_rw [pderiv_one,map_zero, Finset.sum_const_zero]

def melt (k : ℕ) : ShellBook ι →ₗ[ℂ] ℂ := (aeval (0:ι → ℂ)).toLinearMap.comp (hot ι^k)

omit [DecidableEq ι] in
lemma melt_at (k : ℕ) (p : ShellBook ι) : melt (ι:=ι) k p=aeval (0:ι → ℂ) ((hot ι^k) p) := rfl
omit [DecidableEq ι] in
lemma melt_step (k : ℕ) (p : ShellBook ι) : melt (k+1) p=melt k (hot ι p) := by rw [melt_at, melt_at,pow_succ]; rfl
omit [DecidableEq ι] in
lemma melts_low (x : Bean ι) {n k : ℕ} (h : n≠2*k) : melt k ((laser x)^n)=0 := by
  induction k generalizing n with
  | zero =>
    rw [melt_at,pow_zero]; change aeval (0 : ι → ℂ) (laser x^n)=0; rw [map_pow]; simp only [laser,map_sum,map_smul,aeval_X,Pi.zero_apply,smul_zero,Finset.sum_const_zero]; rw [zero_pow h]
  | succ k ih =>
    rw [melt_step]; obtain _|_|n := n
    · rw [pow_zero,burn_one,map_zero]
    · rw [pow_one,burn_first,map_zero]
    rw [burn, map_smul, ih (by omega),smul_zero]
lemma melt_alive (i : ι) (k : ℕ) : melt k (laser (bat i)^(2*k))≠0 := by
  induction k with
  | zero => exact Ne.symm (by simp [melt])
  | succ k ih =>
    rw [show 2*(k+1)=2*k+2 by omega, melt_step,burn,map_smul,bat_norm]
    exact smul_ne_zero (mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))) (by simp)) ih

variable (r : ℝ)

omit [DecidableEq ι] in
lemma meanable (p : ShellBook ι) : Continuous (fun x:Bean ι ↦ aeval (fun i ↦ (x i:ℂ)) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp only [aeval_C,Algebra.algebraMap_self,RingHom.id_apply]; exact continuous_const
  | add p q h g => simp only [map_add]; exact h.add g
  | mul_X p i h => simp only [map_mul,aeval_X]; exact h.mul (Complex.continuous_ofReal.comp ((EuclideanSpace.proj (𝕜:=ℝ) i).continuous))

def mean (ι : Type) [Fintype ι] (r : ℝ) : ShellBook ι →ₗ[ℂ] ℂ where
  toFun p := ∫ x in closedBall (0:Bean ι) r, aeval (fun i ↦ (x i:ℂ)) p
  map_add' p q := by simp only [map_add]; exact integral_add ((meanable p).continuousOn.integrableOn_compact (isCompact_closedBall ..)) ((meanable q).continuousOn.integrableOn_compact (isCompact_closedBall ..))
  map_smul' t p := by simp [integral_const_mul]
lemma mean_axis (v w : Bean ι) (h : ‖v‖=‖w‖) (n : ℕ) : mean ι r (laser v^n)=mean ι r (laser w^n) := by
  let R : Bean ι≃ₗᵢ[ℝ] Bean ι := Submodule.reflection (Submodule.span ℝ ({v-w}:Set (Bean ι)))ᗮ
  have hs : R v=w := Submodule.reflection_sub h
  unfold mean; simp only [LinearMap.coe_mk,AddHom.coe_mk,map_pow,inner_lase]
  have hR : R ⁻¹' closedBall (0:Bean ι) r=closedBall 0 r := by ext y; simp [dist_eq_norm_sub]
  conv_rhs => rw [← R.measurePreserving.setIntegral_preimage_emb R.toContinuousLinearEquiv.toHomeomorph.isClosedEmbedding.measurableEmbedding,hR]
  simp_rw [←hs,R.inner_map_map]
lemma mean_odd (v : Bean ι) (h : Odd n) : mean ι r ((laser v)^n)=0 := by
  have he := mean_axis r v (-v) (norm_neg v).symm n
  rw [laser_flip, h.neg_pow,map_neg] at he
  linear_combination he/2

/-- Constants defined using the integral along *one* chosen axis. -/
def podium (i : ι) (r : ℝ) (k : ℕ) := mean ι r ((laser (bat i))^(2*k)) / melt k (laser (bat i)^(2*k))
lemma melted (v : Bean ι) (i : ι) (k : ℕ) : mean ι r (laser v^(2*k))=podium i r k*melt k (laser v^(2*k)) := by
  let w := (‖v‖) • bat i
  have hw : ‖v‖=‖w‖ := by simp [w,norm_smul,bat_norm]
  have he : melt k (laser v^(2*k))=melt k (laser w^(2*k)) := by
    induction k with
    | zero => simp [melt_at]
    | succ k ih => rw [show 2*(k+1)=2*k+2 by omega,melt_step,burn,melt_step,burn,map_smul,map_smul,ih,hw]
  rw [he,mean_axis r v w hw, show laser w^ (2*k)= (↑‖v‖:ℂ)^(2*k) • laser (bat i)^(2*k) from ?_,map_smul,map_smul]
  · unfold podium; simp only [smul_eq_mul]; field_simp [melt_alive i k]
  unfold w; rw [laser_smul, ← C_mul', mul_pow]; rw [← map_pow (C (σ:=ι) (R:=ℂ)), C_mul']

def roundMean (i : ι) (M : ℕ) : ShellBook ι→ₗ[ℂ] ℂ := ∑ k∈Finset.range (M+1),podium i r k • melt k
lemma round_at (v : Bean ι) (i : ι) (M : ℕ) (hw : n≤M) : roundMean r i M ((laser v)^n)=mean ι r (laser v^n) := by
  unfold roundMean; rw [LinearMap.sum_apply]
  rcases Nat.even_or_odd n with ⟨k,hk⟩|hk
  · rw [show n=2*k by omega]; rw [Finset.sum_eq_single_of_mem k (by simp; omega)]
    · rw [LinearMap.smul_apply,smul_eq_mul,melted]
    intro j _ hj; rw [LinearMap.smul_apply,melts_low _ (by omega),smul_zero]
  rw [mean_odd r v hk]; obtain ⟨k,hk⟩ := hk
  exact Finset.sum_eq_zero fun j _ ↦ by rw [LinearMap.smul_apply,melts_low _ (by omega),smul_zero]

end YM.SchemeConversionRG11.Corona
