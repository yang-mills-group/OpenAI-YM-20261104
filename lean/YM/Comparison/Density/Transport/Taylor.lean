import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Point
import YM.Next.WARD_BIN.Lies

/-!
# From small ordinary jets to scaled derivative prices on a ball

This is Taylor's estimate applied to each ordered derivative, including
when the requested derivative order exceeds the truncation. We scale inputs,
not outputs; directions in the represented norm will have threshold cost per
derivative. No complex continuation/domain assumptions on a masked product.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Transport
open Function Lattice RG Wilson MeasureTheory Filter WardBin.Lies
open AnalyticBridge.SectorAffine.Offset
open scoped Topology BigOperators ContDiff

variable {E D F : Type} [NormedAddCommGroup E] [NormedAddCommGroup D] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ D] [NormedSpace ℝ F]

def dilation (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (w : ℝ) :=
    w • ContinuousLinearMap.id ℝ E

@[simp] lemma dilation_eval (x : E) (w : ℝ) : dilation E w x= w • x := rfl

lemma dil_cost {j : ℕ} {w c : ℝ} (hw : 0 ≤ w) (f : E→ D) (x : E)
    (h : ContDiffAt ℝ j f (w • x)) (hf : ‖iteratedFDeriv ℝ j f (w • x)‖ ≤ c) :
    ‖iteratedFDeriv ℝ j (f ∘ dilation E w) x‖ ≤ c*w^j := by
  rw [liner _ h]; refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans ?_
  rw [Finset.prod_const, Finset.card_univ,Fintype.card_fin]; refine mul_le_mul hf (pow_le_pow_left₀ (norm_nonneg _) ?_ _) (pow_nonneg (norm_nonneg _) _) ((norm_nonneg _).trans hf)
  unfold dilation; rw [norm_smul,Real.norm_of_nonneg hw]; exact mul_le_of_le_one_right hw ContinuousLinearMap.norm_id_le

lemma through_le {w : ℝ} {f : E→ D} {x : E} {i j : ℕ} (h : Through j f x w) (hi : i≤j) :
    Through i f x w := ⟨h.smooth.of_le (Nat.cast_le.mpr hi),fun _ hk=>h.pay _ (hk.trans hi)⟩

lemma through_value {w : ℝ} {f : E→ D} {x : E} {i : ℕ} (h : Through i f x w) : ‖f x‖≤w := by
  simpa using h.pay 0 (Nat.zero_le _)

lemma through_sum {ι : Type*} (s : Finset ι) (c : ι→ℝ) (f : ι→E→D) (n : ℕ) (x : E)
    (h : ∀ i∈s,Through n (f i) x (c i)) : Through n (∑ i∈s,f i) x (∑ i∈s,c i) := by
  classical
  induction s using Finset.induction_on with
  | empty=> simpa using (show Through n (0:E→ D) x 0 from ⟨contDiffAt_const, by
      intro k _; by_cases hz:k=0
      · subst k; simp
      simp [show (0:E→D)=(fun _=> (0:D)) from rfl]⟩)
  | insert a s ha hs=>
    have ih:=hs fun i hi=>h i (by simp [hi]); have hh:=h a (by simp)
    rw [Finset.sum_insert ha,Finset.sum_insert ha]; refine ⟨hh.smooth.add ih.smooth, fun i hi => ?_⟩
    rw [iteratedFDeriv_add_apply (through_le hh hi).smooth (through_le ih hi).smooth]
    exact (norm_add_le ..).trans (add_le_add (hh.pay i hi) (ih.pay i hi))

lemma through_pull {f : E→ D} {x : F} {t : ℝ} {i : ℕ} (L : F →L[ℝ] E) (hL : ‖L‖ ≤ 1)
    (he : Through i f (L x) t) : Through i (f ∘ L) x t := by
  refine ⟨he.smooth.comp x L.contDiff.contDiffAt,fun j hj=>?_⟩
  rw [liner _ (through_le he hj).smooth]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans
  refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans (he.pay j hj)
  rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; exact pow_le_one₀ (norm_nonneg _) hL

lemma through_pi {ι : Type} [Fintype ι] {j : ℕ} {f : E → ι → D} {x : E} {u : ℝ}
    (hu : 0 ≤ u) (h : ∀ i,Through j (fun y=>f y i) x u) : Through j f x u := by
  have H : ContDiffAt ℝ j f x := contDiffAt_pi.mpr fun i=> (h i).smooth
  refine ⟨H,fun e he=> ContinuousMultilinearMap.opNorm_le_bound hu fun p=>?_⟩
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hu (Finset.prod_nonneg fun _ _ => norm_nonneg _))).2
  intro i
  let L : (ι→D) →L[ℝ] D:=ContinuousLinearMap.proj i
  change ‖L (iteratedFDeriv ℝ e f x p)‖ ≤ u* _
  rw [show L (iteratedFDeriv ℝ e f x p)=iteratedFDeriv ℝ e (L∘f) x p by rw [L.iteratedFDeriv_comp_left H (by exact_mod_cast he)]; rfl]
  exact ((ContinuousMultilinearMap.le_opNorm _ _)).trans (mul_le_mul_of_nonneg_right ((h i).pay e he) (Finset.prod_nonneg fun _ _=> norm_nonneg _))

private theorem recover (s m : ℕ) (e d : ℝ) {f : E → F} (hm : s≤m)
    (he : 0≤e) (hd : 0≤d)
    (hc : ∀ x : E, ‖x‖ ≤ 1 → ContDiffAt ℝ m f x)
    (hF : ∀ j<s, ‖iteratedFDeriv ℝ j f 0‖ ≤ e)
    (hH : ∀ x : E, ‖x‖ ≤ 1 → ∀ j, s≤j → j≤m → ‖iteratedFDeriv ℝ j f x‖ ≤ d)
    (x : E) (hx : ‖x‖ ≤ 1) : Through m f x (s*e + d) := by
  have Y (i j : ℕ) (hi : i+j=s) (z : E) (hz : ‖z‖≤1) : ‖iteratedFDeriv ℝ j f z‖ ≤ i*e+d := by
    induction i generalizing j z with
    | zero =>
      have ht : s=j := by omega
      rw [← ht]; simpa using hH z hz s le_rfl hm
    | succ i ih=>
      have hj : j<s := by omega
      let K:= Metric.closedBall (0:E) 1
      have hu (y : E) : y∈K ↔ ‖y‖≤1 := by simp [K]
      let H := iteratedFDeriv ℝ j f
      have HH (y) (hy : y∈K) : DifferentiableAt ℝ H y :=
        (hc y ((hu y).1 hy)).differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr (lt_of_lt_of_le hj hm))
      have HH' : ‖H z-H 0‖ ≤ (i*e+d)*‖z‖ := by
        simpa only [sub_zero] using (convex_closedBall (0:E) 1).norm_image_sub_le_of_norm_fderiv_le HH
          (fun y (hy:y∈K)=> (norm_fderiv_iteratedFDeriv (𝕜:=ℝ)).trans_le (ih (j+1) (by omega) _ ((hu _).1 hy))) ((hu 0).2 (by simp)) ((hu z).2 hz) -- check field
      refine (norm_le_insert' H z (0:E)).trans ?_
      refine (add_le_add (hF j hj) (HH'.trans (mul_le_of_le_one_right (by positivity) hz))).trans_eq ?_; push_cast; ring
  refine ⟨hc x hx,fun j hj=>?_⟩
  by_cases hz:s≤j
  · exact (hH x hx j hz hj).trans (le_add_of_nonneg_left (by positivity))
  apply (Y (s-j) j (by omega) x hx).trans; gcongr
  exact Nat.sub_le ..
where
  norm_le_insert' {F' : Type} [NormedAddCommGroup F'] (f : E→F') (z y : E) : ‖f z‖ ≤ ‖f y‖ + ‖f z - f y‖ := by -- need generic add Norm type
    calc
      _ = ‖f y + (f z - f y)‖ := by rw [add_sub_cancel]
      _ ≤ _ := norm_add_le ..

/-- On the actual real log domain. Keep valuation `s`, independent of m.
When comparing through order `S` use `s=S+1` (augmented for negative
prefactors). When charging a positively graded short atom even before
coefficient comparison, take `e=0`, and the valuation of that atom. -/
theorem rescale (s m : ℕ) (w d e : ℝ) (f : E → F) (hw : 0≤w) (hl : w≤1) (hd : 0≤d) (he : 0≤e) (hm : s≤m)
    (h : ∀ x : E, ‖x‖ ≤ w → Through m f x d)
    (hF : ∀ j<s, ‖iteratedFDeriv ℝ j f 0‖ ≤ e)
    (x : E) (hx : ‖x‖ ≤ 1) : Through m (f ∘ dilation E w) x (s*e+d*w^s) := by
  have hu (y : E) (hy : ‖y‖≤1) : Through m f (w • y) d:= h _ (by rw [norm_smul,Real.norm_of_nonneg hw]; exact mul_le_of_le_one_right hw hy)
  apply recover s m e (d*w^s) hm he (by positivity) (fun y hy => (hu y hy).smooth.comp y (dilation E w).contDiff.contDiffAt) ?_ ?_ x hx
  · intro i hi
    refine le_trans (dil_cost hw f 0 (through_le (hu 0 (by simp)) (hi.le.trans hm)).smooth (c:=e) ?_) (mul_le_of_le_one_right he (pow_le_one₀ hw hl))
    simpa only [smul_zero] using! hF i hi
  intro y hy i hi hk
  exact (dil_cost hw f y (through_le (hu y hy) hk).smooth ((hu y hy).pay i hk)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hw hl hi) hd)
end YM.Comparison.Density.Transport
