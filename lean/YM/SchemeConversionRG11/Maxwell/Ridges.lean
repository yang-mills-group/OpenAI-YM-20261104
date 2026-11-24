import YM.SchemeConversionRG11.Maxwell.Muted

/-! # Read constants by escaping all correlations -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter Maxwell Maxwell.Free Wick Tensor Set MvPolynomial
open scoped Topology BigOperators ComplexOrder

variable {G : Gauge} {n m k l : ℕ} {X : Points n}
lemma stretches (hx : X∈conf _) {t : ℝ} (ht : t≠0) : t • X∈conf _ :=
  fun i j e ↦ (show Injective X.ofLp from hx) (smul_right_injective E4 ht (show t • X i=t • X j from e))
lemma entry_escapes (u v : Slot G) {x y : E4} (h : x≠y) : Tendsto (fun t:ℝ ↦ entry u v (t • x) (t • y)) atTop (𝓝 0) := by
  let q := 4+u.1+v.1
  have ht : Tendsto (fun x:ℝ ↦ x⁻¹^q) atTop (𝓝 0) := by simpa only [zero_pow (n:=q) (by unfold q; omega)] using tendsto_inv_atTop_zero (𝕜:=ℝ) |>.pow q
  have hh := (ht.smul_const (entry u v x y)); rw [zero_smul] at hh
  apply hh.congr'; filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  unfold entry; rw [← smul_sub, (kernel_pole _ _).degree t ht _ (sub_ne_zero.mpr h)]
  unfold q; simp [Complex.real_smul]
open Occ
lemma mono_escapes (hx : X∈conf _) {W : Powers G n} (h : W ≠ 0) : Tendsto (fun t:ℝ ↦ Wick.monomial (t • X) W) atTop (𝓝 0) := by
  classical
  obtain ⟨i,k,hi⟩ : ∃ i k, W i k>0 := by by_contra! ht; exact h (funext fun i ↦ Finsupp.ext fun k ↦ Nat.eq_zero_of_le_zero (ht i k))
  let v : Occ W := Occ.atSlot i k 0 hi
  have hg (P : Matching W) : Tendsto (fun t:ℝ ↦ graph (t • X) P) atTop (𝓝 0) := by
    have he (w : Occ W) : Tendsto (fun t:ℝ ↦ edge (t • X) w (partner P w)) atTop (𝓝 0) := entry_escapes _ _ ((show Injective X.ofLp from hx).ne (different _ _).symm)
    have hw := tendsto_finsetProd (corners P) (fun i _ ↦ he i)
    rwa [show ∏ _i∈corners P,(0:ℂ)=0 from Finset.prod_eq_zero (inside P v) rfl] at hw
  have ht := tendsto_finsetSum Finset.univ (fun i _ ↦ hg i)
  simp only [Finset.sum_const_zero] at ht; exact ht

def floatL (n : ℕ) (G : Gauge) : MultilinearMap ℂ (fun _ : Fin n ↦ WickPol G) ℂ := (MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compLinearMap fun _ ↦ (aeval (0:Slot G → ℂ)).toLinearMap
lemma floats (hx : X∈conf _) (W : Fin n→WickPol G) : Tendsto (fun t:ℝ ↦ moment G (t • X) W) atTop (𝓝 (∏ i, aeval (0:Slot G→ℂ) (W i))) := by
  classical
  change Tendsto _ _ (𝓝 (floatL n G W))
  conv => arg 1; ext; rw [Multilabel.expansion (fun _ ↦ monBasis G)]
  rw [Multilabel.expansion (fun _ ↦ monBasis G) (floatL _ _)]
  apply tendsto_finsetSum; intro b hb; apply Tendsto.const_smul
  change Tendsto (fun t : ℝ ↦ moment G _ (fun i ↦ monBasis G (b i))) _ (𝓝 (∏ i, aeval (0:Slot G→ℂ) (monBasis G (b i))))
  have he p : aeval (0:Slot G→ℂ) (monBasis G p)=MvPolynomial.coeff 0 (monBasis G p) := aeval_zero' _
  rcases eq_or_ne b 0 with hg|hg
  · subst b; simp [monBasis]; exact tendsto_const_nhds.congr' (Eventually.of_forall (fun _ ↦ (Wick.constants _).symm))
  choose i hi using (show ∃ i,b i ≠ 0 by by_contra! ht; exact hg (funext ht))
  simp_rw [moment_basis]; rw [Finset.prod_eq_zero (Finset.mem_univ i)]
  · exact mono_escapes hx hg
  rw [he]; simp [monBasis,hi]

variable {ι : Type*} [Fintype ι]
lemma muted_ice {p : ι → ℂ} {W : Panel ι n G} (h : Muted p W) : ∑ i:ι,p i * ∏ j,aeval (0:Slot G→ℂ) (W i j)=0 := by
  let x := points fun i : Fin n ↦ (↑i.val:ℝ) • basis 0
  have hx : x∈conf n := by
    intro i j h; apply Fin.ext; have hh := congr_arg (fun v:E4 ↦ v 0) h; simpa [x] using hh
  refine tendsto_nhds_unique (f:=fun t:ℝ ↦ ∑ i:ι,p i * moment G (t • x) (W i)) (l:=atTop) (tendsto_finsetSum _ fun i _ ↦ (floats hx (W i)).const_mul _) ?_
  apply tendsto_const_nhds.congr'; filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht; exact (muted_direct h (stretches hx ht.ne')).symm
end YM.SchemeConversionRG11.Corona
