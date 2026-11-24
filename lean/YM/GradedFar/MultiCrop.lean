import YM.GradedFar.Penultimate
/-!
# Continuation: many separately cropped factors

Estimate the products arising at the first inequality in (M.2). Again with s=log T acts on
geometry (and charges) but held fixed in *all* formal-series operations, including in powers of
column parameters. These lemmas are useful e.g. when replacing Far arguments by a more accurate
crop, at any order extension, in that comparison. ChargeP proved on the same estimates as the
already retained series in GradedFar. Here too factor out **evaluation** to the first omitted
power and show this error has homogeneous price on the remaining coefficients; therefore it
costs evaluation to the `(p+1)` times those power and log terms. Key: no factor needs to have
weight zero, nor to be independent of s, and charges add (joint costs, rather than a price
assuming coefficientwise bounded all the way out to a given moving r).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set PowerSeries
open XSpace XSpace.Normalize XSpace.Structure1 Scale
open Dframe O O.Score O.Enh
open scoped Topology BigOperators Classical

section many
variable {I : Type} {J : Type} {p q : ℕ} {a b : ℝ}
variable {F G : I → ℝ → PowerSeries ℂ} {f g : I → ℝ → ℂ} {z : I → ℝ}
/-- z^(p+1) times a log power cost with exponent a in T-decay -/
def Omitted (z : I → ℝ) (p : ℕ) (a : ℝ) (f : I → ℝ → ℂ) :=
    ∃ g : I → ℝ → ℂ, Rain a g ∧ ∀ i s, f i s = (z i : ℂ)^(p+1) * g i s
namespace Omitted
lemma zero : Omitted z p a (fun _ _ => 0) := ⟨_,Rain.nil a,fun _ _ => (mul_zero _).symm⟩
lemma congr (h : Omitted z p a f) (he : ∀ i s, f i s = g i s) : Omitted z p a g :=
  (funext fun i => funext (he i)) ▸ h
lemma add (h : Omitted z p a f) (h' : Omitted z p a g) : Omitted z p a (fun i s => f i s + g i s) := by
  obtain ⟨X,h,k⟩ := h; obtain ⟨Y,h',k'⟩ := h'
  exact ⟨ _, Rain.plus h h', fun i s => by dsimp; rw [k, k', mul_add] ⟩
lemma sum (s : Finset J) {f : J → I → ℝ → ℂ} (h : ∀ i ∈ s, Omitted z p a (f i)) :
    Omitted z p a (fun i t => ∑ j ∈ s, f j i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; apply zero
  | insert _ i hi ih =>
    simp_rw [Finset.sum_insert hi]; exact add (h _ (Finset.mem_insert_self ..))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
lemma mul_left (h : Rain a f) (he : Omitted z p b g) : Omitted z p (a+b) (fun i s => f i s * g i s) := by
  obtain ⟨X,h',k⟩ := he; exact ⟨_, Rain.mul h h', fun i s => by dsimp; rw [k, mul_left_comm] ⟩
lemma mul_zero_left (h : Rain 0 f) (he : Omitted z p b g) : Omitted z p b (fun i s => f i s * g i s) := by
  simpa only [zero_add] using mul_left h he
lemma mul_right (h : Omitted z p a f) (he : Rain b g) : Omitted z p (a+b) (fun i s => f i s * g i s) := by
  obtain ⟨X,h',k⟩ := h; exact ⟨_, Rain.mul h' he, fun i s => by dsimp; rw [k, mul_assoc] ⟩
theorem budget (h : Omitted z p a f) : ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ᶠ s in atTop,
    ∀ i, ‖f i s‖ ≤ |z i|^(p+1)*(C*post a s k) := by
  obtain ⟨g,⟨C,hC,k,h⟩,k'⟩ := h; refine ⟨ C,hC,k,h.mono fun s hs i => ?_ ⟩
  rw [k',norm_mul,norm_pow,Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hs i) (by positivity)
end Omitted

lemma crop_product_omitted (hF : ChargeP (p+1) a F) (hG : ChargeP (p+1) b G) (hz : ∀ i, |z i| ≤ 1) :
    Omitted z p (a+b) (fun i s => crop p (z i) (F i s) * crop p (z i) (G i s) -
      crop p (z i) (F i s * G i s)) := by
  refine ⟨fun i s => overrun p (z i) (F i s) (G i s), ?_, fun i s => ?_⟩
  · unfold overrun; refine Rain.sum _ fun j hj => ?_
    obtain ⟨h,h',_⟩ := skipped_spec j hj
    exact Rain.cover (clock_cash hz _) (Rain.mul (hF j.1 h) (hG j.2 h'))
  · dsimp only; rw [separate, add_sub_cancel_left]
lemma crop_extension_omitted (hF : ChargeP (q+1) a F) (hp : p ≤ q) (hz : ∀ i, |z i| ≤ 1) :
    Omitted z p a (fun i s => crop q (z i) (F i s) - crop p (z i) (F i s)) := by
  simp_rw [crop_eq, ← Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ hp)]; apply Omitted.sum
  intro j hj; have h := Finset.mem_Ico.mp hj
  exact ⟨ _, Rain.cover (clock_cash hz (j-(p+1))) (hF j h.2), fun i s => by
    dsimp only; rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le h.1] ⟩

lemma product_charge (s : Finset J) {F : J → I → ℝ → PowerSeries ℂ} {a : J → ℝ}
    (h : ∀ i ∈ s, ChargeP p (a i) (F i)) : ChargeP p (∑ i ∈ s, a i) (fun i t => ∏ j ∈ s, F j i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty]; exact ChargeP.fixed _
  | insert j s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]; exact ChargeP.joint
      (h _ (Finset.mem_insert_self ..)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Charge all terms from pricing the factors at q and through-p, and from
forming the actual product with the series G through p.
Charges can be negative (growth) compensated by other factors. -/
theorem many_omitted (s : Finset J) {F : J → I → ℝ → PowerSeries ℂ} {a : J → ℝ}
    (hF : ∀ i ∈ s, ChargeP (q+1) (a i) (F i)) (hG : ChargeP (p+1) b G) (hp : p ≤ q)
    (hz : ∀ i, |z i| ≤ 1) : Omitted z p ((∑ i ∈ s, a i) + b)
      (fun i t => (∏ j ∈ s, crop q (z i) (F j i t)) * crop p (z i) (G i t) -
        crop p (z i) ((∏ j ∈ s, F j i t) * G i t)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, one_mul, sub_self]; exact Omitted.zero
  | insert j s hs ih =>
    let α := ∑ i ∈ s, a i
    let Y (i : I) (t : ℝ) := ∏ j ∈ s, F j i t
    have h : ∀ i ∈ s, ChargeP (q+1) (a i) (F i) := fun i hi => hF i (Finset.mem_insert_of_mem hi)
    let H := fun i t => Y i t * G i t
    have hH : ChargeP (p+1) (α+b) H := ChargeP.joint
      (ChargeP.move (product_charge s h) (Nat.succ_le_succ hp)) hG
    have hj := hF _ (Finset.mem_insert_self ..)
    -- pull out j. Charge every overrun, either from higher powers of j, from the new
    -- through-p product, or recursively from the tail products.
    have hf := Omitted.mul_left (rain_crop hj hz) (ih h)
    have hw := Omitted.mul_right (crop_extension_omitted hj hp hz) (rain_crop hH hz)
    have he := (hf.add hw).add (crop_product_omitted (ChargeP.move hj (Nat.succ_le_succ hp)) hH hz)
    rw [Finset.sum_insert hs, add_assoc]
    refine Omitted.congr he ?_
    intro i t; dsimp only [Y,H]; simp only [Finset.prod_insert hs]; rw [mul_assoc (F j i t)]; ring
end many
end YM.FVA2.GradedFar
