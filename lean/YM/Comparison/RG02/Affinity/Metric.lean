import YM.Comparison.RG02.Affinity.Vibe
import YM.Push.LOOP_COEFFICIENT.Vector
import Mathlib.Analysis.Calculus.ImplicitContDiff
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Affinity
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree
open YM.Precision YM.Next.SectorChange
open Matrix
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I : Type} [Fintype I] [DecidableEq I]
local notation "Λ" => I→ℝ

/-!
 # Analytic square (real germ about the flat Hessian); no diagonal division

 Frobenius norm here, no volume-comparison estimates. Implicit branch about a possibly
 repeated-eigenvalue metric. -/
namespace MetricFix
open Gaussian
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
local notation "M"=> Matrix I I ℝ
variable {f : X→Matrix I I ℝ} (hf : ContDiffAt ℝ ω f 0) (hQ : (f 0).PosDef)
local notation "O"=> f 0
local notation "u"=> ((0:X),f 0)

private def calcify (A : X→Matrix I I ℝ) (y : X × Matrix I I ℝ) := y.2*(A 0)⁻¹*y.2-A y.1
include hf in
omit [FiniteDimensional ℝ X] in
private lemma df : ContDiffAt ℝ ω (calcify f) u := ((contDiffAt_snd.mul contDiffAt_const).mul contDiffAt_snd).sub (hf.comp (f:=Prod.fst) u contDiffAt_fst)
include hQ in
omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
private lemma exactify : calcify f u=0 := by
  unfold calcify; simp [(f 0).mul_nonsing_inv (IsUnit.mk0 _ hQ.det_pos.ne')]
include hf hQ
local notation "L"=> (fderiv ℝ (calcify f) u ∘L ContinuousLinearMap.inr ℝ X (Matrix I I ℝ))
omit [FiniteDimensional ℝ X] in
private lemma d_cal (v : M) : L v= (2:ℝ) • v := by
   let B : X × (Matrix I I ℝ) →L[ℝ] Matrix I I ℝ := .snd ..
   have hd := (((B.hasFDerivAt (x:=u)).mul' (hasFDerivAt_const O⁻¹ u)).mul' B.hasFDerivAt).sub ((hf.differentiableAt (by simp)).hasFDerivAt.comp u ((ContinuousLinearMap.fst ℝ X M).hasFDerivAt))
   rw [ContinuousLinearMap.comp_apply, show fderiv ℝ (calcify f) u =_ from hd.fderiv]
   change O*O⁻¹*v + (O*0+v*O⁻¹)*O - fderiv ℝ f 0 0=_
   have h := IsUnit.mk0 _ hQ.det_pos.ne'
   rw [Matrix.mul_zero,zero_add,Matrix.mul_assoc v,(f 0).mul_nonsing_inv h,(f 0).nonsing_inv_mul h, Matrix.one_mul,Matrix.mul_one,map_zero,sub_zero,show (2:ℝ)=1+1 by norm_num,add_smul,one_smul] -- map_zero scope

omit [FiniteDimensional ℝ X] in
private lemma warm : (L).IsInvertible := by
   apply ContinuousLinearMap.IsInvertible.of_inverse (g:=(1/2:ℝ) • ContinuousLinearMap.id _ M)
   all_goals
      ext1 v; simp only [ContinuousLinearMap.comp_apply, d_cal hf hQ, _root_.smul_apply,ContinuousLinearMap.id_apply]; norm_num [smul_smul]

def minted := (df hf).implicitFunction (by simp) (warm hf hQ)
lemma minted_at_zero : minted hf hQ 0= f 0 := (df hf).implicitFunction_apply_self ..
lemma mint_smooth : ContDiffAt ℝ ω (minted hf hQ) 0 := (df hf).contDiffAt_implicitFunction ..
local notation "A"=> minted hf hQ

lemma makes : ∀ᶠ x in 𝓝 0, A x * (f 0)⁻¹ * A x=f x := by
   filter_upwards [(df hf).eventually_apply_implicitFunction (by simp) (warm hf hQ)] with x hx
   exact sub_eq_zero.mp (hx.trans (exactify hQ))
variable (hi : ∀ᶠ x in 𝓝 0, (f x).IsSymm)
include hi
lemma remains : ∀ᶠ x in 𝓝 0, (A x).IsSymm := by
   have h := show (O).transpose=O from Matrix.isHermitian_iff_isSymm.mp hQ.isHermitian
   have ht : ContDiffAt ℝ ω (fun x=> (A x).transpose) 0 := YM.Push.Loops.smooth_transpose (mint_smooth hf hQ)
   have he : Tendsto (fun x=> (x,(A x).transpose)) (𝓝 0) (𝓝 ((0:X), O)) := by
      have hH : (A 0).transpose=O:= by rw [minted_at_zero,h];
      exact tendsto_id.prodMk_nhds (hH ▸ ht.continuousAt.tendsto)
   filter_upwards [he.eventually ((df hf).eventually_apply_eq_iff_implicitFunction (by simp) (warm hf hQ)), hi, makes hf hQ] with x hx hK hv
   apply Eq.symm (hx.mp _); rw [exactify hQ]; change (A x).transpose*O⁻¹*(A x).transpose - f x=0
   apply sub_eq_zero.mpr; conv_rhs => rw [← hK.eq, ← hv]
   rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_nonsing_inv,h,Matrix.mul_assoc]
-- use inverse on RIGHT. Need (B x)^T f x (B x)=O. with f x=A O⁻¹ A this is B=A⁻¹ * O.

def blanker (x:X) : M := (minted hf hQ x)⁻¹ * f 0
omit hi in
lemma blanked : blanker hf hQ 0=1:= by unfold blanker; rw [minted_at_zero,Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ hQ.det_pos.ne')]
omit hi in
lemma blank_smooth : ContDiffAt ℝ ω (blanker hf hQ) 0 := by
   have ht := YM.Push.Loops.inv_contDiffAt (minted hf hQ 0) (by rw [minted_at_zero]; exact (IsUnit.mk0 _ hQ.det_pos.ne')); exact (ht.comp _ (mint_smooth hf hQ)).mul contDiffAt_const
lemma blank_cost : ∀ᶠ x in 𝓝 0,(blanker hf hQ x).transpose*f x*blanker hf hQ x= f 0 := by
   have ht := IsUnit.mk0 _ hQ.det_pos.ne'
   have hd := (YM.Push.Loops.det_contDiff.contDiffAt.comp 0 (mint_smooth hf hQ)).continuousAt
   have hz : ∀ᶠ x in 𝓝 0, (A x).det ≠ 0 := hd.eventually_ne (by unfold Function.comp; rw [minted_at_zero]; exact ht.ne_zero)
   filter_upwards [hz,makes hf hQ,remains hf hQ hi] with x h hb ha
   have hv := IsUnit.mk0 _ h
   have hO : Matrix.transpose (f 0)=_ := show (O).transpose=O from Matrix.isHermitian_iff_isSymm.mp hQ.isHermitian
   unfold blanker; rw [← hb, Matrix.transpose_mul,Matrix.transpose_nonsing_inv,hO, ha]
   rw [Matrix.mul_assoc _ (A x)⁻¹, ← Matrix.mul_assoc (A x)⁻¹, ← Matrix.mul_assoc (A x)⁻¹,Matrix.nonsing_inv_mul _ hv, Matrix.one_mul,← Matrix.mul_assoc O,Matrix.mul_nonsing_inv _ ht,Matrix.one_mul,← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hv,Matrix.one_mul]
end MetricFix
end YM.Comparison.RG02.Affinity
