import YM.Work.G05.Taylor
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Shellac.Pine

/-!
# Remainders with a drifting polynomial candidate

On auxiliary volumes the normed spaces need not be fixed. Take care of dimension and
also near-but-not-exact Taylor jets (the comparison uses untruncated formal Gaussian
integration vs true moving real domains). No unspecified constants depend on those spaces.
Real `blockTaylor` convention, *all* normalized Fréchet derivatives (not diagonal only).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxJets
open Function Metric Set
open ConnectedActivityE6 Blaze Brush PhysicalNext.Repeat Work.G05
open scoped Topology ContDiff BigOperators Classical
variable {E F H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {k n : ℕ} {f g : E → F}

lemma trunc_above (h : ContDiffAt ℝ k g 0) : ∀ j, k < j →
    ∀ x, iteratedFDeriv ℝ j (blockTaylor k g) x=0 := by
  induction k generalizing g with
  | zero =>
    have hr : blockTaylor 0 g=fun _=>g 0:=by
      ext x
      rw [blockTaylor,Nat.zero_add,Finset.sum_range_one]
      exact Tensor.coeff_apply_zero g 0 _
    intro i hi x
    obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi)
    rw [hr,iteratedFDeriv_succ_const]; rfl
  | succ k ih=>
    intro i hi x
    obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    ext1 y
    cases y using Fin.consCases with | cons u v=>
      have he := Analysis.cons_inner (j:=i) (f:=blockTaylor (k+1) g) (x:=x)
        (blockTaylor_contDiff ..|>.contDiffAt) u v
      rw [he, D_blockTaylor h,
        ih (Analysis.dSmooth h u (by push_cast; rfl)) i (by omega) x]; rfl

lemma drifting {C b a : ℝ} (ha : 0 < a) (he : a ≤ 1) (hk : k < n) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hf : ∀ x ∈ ball 0 a, ContDiffAt ℝ n f x)
    (H : ∀ i, k < i → i ≤ n → ∀ x ∈ ball 0 a, normJ i f x ≤ C)
    (hg : ContDiffAt ℝ k g 0)
    (ht : Brush k b 1 (f-g) 0) : ∀ x ∈ ball (0:E) a,
    Brush n (C*a^(k+1) + (k+1:ℕ)*b) a⁻¹ (f-blockTaylor k g) x := by
  apply Shellac.pools ha he hk hC hb
  · intro i hi
    exact (hf i hi).sub ((blockTaylor_contDiff ..).contDiffAt)
  · intro i hi hh x hx
    unfold normJ; rw [iteratedFDeriv_sub_apply ((hf _ hx).of_le (Nat.cast_le.mpr hh)) ((blockTaylor_contDiff ..).contDiffAt), trunc_above hg _ hi x, sub_zero]; exact H i hi hh x hx
  intro i hi
  let f' := f-blockTaylor k g
  have h₀ : ContDiffAt ℝ (↑i) f 0:= (hf _ (mem_ball_self ha)).of_le (Nat.cast_le.mpr (by omega))
  unfold normJ
  rw [iteratedFDeriv_sub_apply h₀ (blockTaylor_contDiff ..|>.contDiffAt), blockTaylor_jets hg i (Nat.le_of_lt_succ hi), ← iteratedFDeriv_sub_apply h₀ (hg.of_le (Nat.cast_le.mpr (Nat.le_of_lt_succ hi)))]
  exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ ha.le he)).trans ((Brush.offer.1 ht).2 _ (Nat.le_of_lt_succ hi))

lemma same_trunc {C a : ℝ} (ha : 0 < a) (he : a ≤ 1) (hk : k < n) (hC : 0 ≤ C)
    (hf : ∀ x ∈ ball 0 a, ContDiffAt ℝ n f x)
    (H : ∀ i, k < i → i ≤ n → ∀ x ∈ ball 0 a,normJ i f x ≤ C) :
    ∀ x∈ball 0 a, Brush n (C*a^(k+1)) a⁻¹ (f-blockTaylor k f) x:= by
  have hz : Brush k 0 1 (f-f) 0:=by
    rw [sub_self]; simpa only [norm_zero] using! Brush.certified (x:=(0:E)) (k:=k) zero_le_one (0:F)
  simpa only [mul_zero, add_zero] using drifting ha he hk hC (le_refl 0) hf H ((hf _ (mem_ball_self ha)).of_le (by exact_mod_cast hk.le)) hz

-- Polynomial-size continuity budget for algebra capabilities, even when the finite
-- dimensional space changes. Use on log / inversion / unscaled auxiliary readouts.
def partCount (k : ℕ) : ℝ := ∑ i∈Finset.range (k+1), (Fintype.card (OrderedFinpartition i) : ℝ)
def continuityFee (k : ℕ) (B C ε : ℝ) := partCount k*(C*k*B^k*ε+(C*ε)*B^k)
lemma composition_diff {x : E} {U : F → H} {s : Set F} (hs : Convex ℝ s)
    {B C ε : ℝ} (hB : 1 ≤ B) (h : ∀ y∈s, Brush (k+1) C 1 U y)
    (hi : f x ∈ s) (hj : g x ∈ s) (hf : Brush k B 1 f x) (hg : Brush k B 1 g x)
    (he : Brush k ε 1 (f-g) x) : Brush k (continuityFee k B C ε) 1 ((U ∘ f)-(U ∘ g)) x:= by
  have hV := ((h _ hi).smaller (show k ≤ k+1 by omega)).smooth
  have hW := ((h _ hj).smaller (show k ≤ k+1 by omega)).smooth
  have hx:= hV.comp x hf.smooth; have hy:= hW.comp x hg.smooth
  have hC:= (h _ hi).nonneg; have hε:= he.nonneg
  apply Brush.offer.mpr; refine ⟨hx.sub hy, fun i hK=>?_⟩
  let A:= C*k*B^k*ε+(C*ε)*B^k
  have hp j (hh:j ≤ k) : ‖iteratedFDeriv ℝ j U (f x)-iteratedFDeriv ℝ j U (g x)‖≤ C*ε:= by
    have ht:= hs.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (C:=C) (f:=iteratedFDeriv ℝ j U) (fun y hy=> (h y hy).smooth.differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr (Nat.lt_succ_of_le hh))) (fun y hy=> norm_fderiv_iteratedFDeriv.trans_le ((Brush.offer.1 (h y hy)).2 _ (Nat.succ_le_succ hh))) hj hi
    exact ht.trans (mul_le_mul_of_nonneg_left he.bound hC)
  let d (c : OrderedFinpartition i) := (ftaylorSeries ℝ U (f x)).compAlongOrderedFinpartition (ftaylorSeries ℝ f x) c-(ftaylorSeries ℝ U (g x)).compAlongOrderedFinpartition (ftaylorSeries ℝ g x) c
  have hX (c : OrderedFinpartition i): ‖d c‖ ≤ A:= by
    let L₁ (j:Fin c.length):= iteratedFDeriv ℝ (c.partSize j) f x
    let L₂ (j:Fin c.length):= iteratedFDeriv ℝ (c.partSize j) g x
    have ht j := (c.partSize_le j).trans hK
    have hw₁ : ‖L₁‖ ≤ B := (pi_norm_le_iff_of_nonneg hf.nonneg).2 fun j=> (Brush.offer.1 hf).2 (c.partSize j) (ht j)
    have hm (j) : ‖L₂ j‖ ≤ B:= (Brush.offer.1 hg).2 _ (ht j)
    have hw₂ : ‖L₂‖ ≤ B:= (pi_norm_le_iff_of_nonneg hf.nonneg).2 hm
    have hb : ‖L₁-L₂‖≤ ε:= by
      refine (pi_norm_le_iff_of_nonneg hε).2 fun j=>?_
      have hv:= (Brush.offer.1 he).2 _ (ht j)
      unfold normJ at hv; rw [iteratedFDeriv_sub_apply (hf.smaller (ht j)).smooth (hg.smaller (ht j)).smooth] at hv; exact hv
    have hl:= c.length_le.trans hK
    apply (c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le (iteratedFDeriv ℝ c.length U (f x)) _ L₁ L₂).trans
    apply add_le_add
    · have hw: max ‖L₁‖ ‖L₂‖ ^ (c.length - 1) ≤ B^k := ((pow_le_pow_left₀ ((norm_nonneg L₁).trans (le_max_left ..)) (max_le hw₁ hw₂) _)).trans (pow_le_pow_right₀ hB (by omega))
      apply mul_le_mul _ hb (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hw (by positivity) (by positivity)
      exact mul_le_mul ((Brush.offer.1 (h _ hi)).2 _ (by omega)) (by exact_mod_cast hl) (by positivity) hC
    apply mul_le_mul (hp _ hl) _ (Finset.prod_nonneg (fun _ _=> norm_nonneg _)) (by positivity)
    refine (Finset.prod_le_prod (g:=fun _=>B) (fun _ _=>norm_nonneg _) (fun i _=> hm i)).trans ?_
    simpa using! pow_le_pow_right₀ hB hl
  have hZ : ‖∑ c : OrderedFinpartition i,d c‖ ≤ continuityFee k B C ε:= (norm_sum_le ..).trans ((Finset.sum_le_sum fun c _=>hX c).trans (by
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (ι:=ℕ) (f:=fun i=>(Fintype.card (OrderedFinpartition i):ℝ)) (fun _ _=> Nat.cast_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hK))) (by unfold A; positivity)))
  have hc : (i:WithTop ℕ∞) ≤ (k:WithTop ℕ∞):= Nat.cast_le.mpr hK
  unfold normJ; rw [iteratedFDeriv_sub_apply (hx.of_le hc) (hy.of_le hc), iteratedFDeriv_comp hV hf.smooth hc, iteratedFDeriv_comp hW hg.smooth hc, FormalMultilinearSeries.taylorComp, FormalMultilinearSeries.taylorComp, ←Finset.sum_sub_distrib]; exact hZ

end YM.RGComparison01.AuxJets
