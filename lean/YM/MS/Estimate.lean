import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Power-log estimates for comparing regulators

`Cost.Le` retains an arbitrary power of a specified polynomial cost and a constant.
The first index carries parameters held fixed when differentiating (among which can
be the heat length); the second will usually be a momentum tuple.
This is a one-sided inequality. The norm and the expensive factor are
*not* hidden. `zone` shouldn't then implicitly restrict scales when applying
integration by parts — we'll use smooth extensions with estimates on it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS
open Set Function Real
variable {ι ι' E F α : Type*}

structure Cost (ι E : Type*) where
  zone (i : ι) : Set E
  cheap (i : ι) : E → ℝ
  one_le (i : ι) (p : E) (h : p ∈ zone i) : 1 ≤ cheap i p

namespace Cost
variable {T : Cost ι E} {f g w u v : ι → E → ℝ}

def Le (T : Cost ι E) (f g : ι → E → ℝ) :=
  ∃ (C : ℝ), 0 < C ∧ ∃ b : ℕ, ∀ i p, p ∈ T.zone i → f i p ≤ C * (T.cheap i p)^b * g i p

def NN (T : Cost ι E) (f : ι → E → ℝ) := ∀ i p, p ∈ T.zone i → 0 ≤ f i p

lemma cheap_pos (T : Cost ι E) {i p} (hx : p ∈ T.zone i) : 0 < T.cheap i p :=
  zero_lt_one.trans_le (T.one_le i p hx)

lemma nn_of_le {f g : ι → E → ℝ} (h : T.Le f g) (hf : T.NN f) : T.NN g := by
  obtain ⟨C,hC,b,h⟩ := h
  exact fun i p hx => nonneg_of_mul_nonneg_right ((hf i p hx).trans (h i p hx))
    (mul_pos hC (pow_pos (T.cheap_pos hx) _))

lemma of_le (h : ∀ i p, p ∈ T.zone i → f i p ≤ g i p) : T.Le f g := by
  refine ⟨1, zero_lt_one, 0, fun i p hx => ?_⟩
  simpa using h i p hx

lemma refl (T : Cost ι E) (f : ι → E → ℝ) : T.Le f f := of_le fun _ _ _ => le_rfl

lemma Le.trans (hf : T.Le f g) (hg : T.Le g w) : T.Le f w := by
  obtain ⟨C,hC,b,hf⟩ := hf
  obtain ⟨D,hD,c,hg⟩ := hg
  refine ⟨C*D, mul_pos hC hD, b+c, fun i p hx => ?_⟩
  calc
    f i p ≤ _ := (hf i p hx).trans (mul_le_mul_of_nonneg_left (hg i p hx) ?_)
    _ = _ := by rw [pow_add]; ring
  exact mul_nonneg hC.le (pow_nonneg (T.cheap_pos hx).le _)

lemma Le.left (h : T.Le f g) (w' : ∀ i p, p ∈ T.zone i → u i p ≤ f i p) : T.Le u g :=
  Le.trans (of_le w') h

lemma Le.right (h : T.Le f g) (w' : ∀ i p, p ∈ T.zone i → g i p ≤ u i p) : T.Le f u :=
  h.trans (of_le w')

lemma Le.mul (h : T.Le f g) (h' : T.Le u v) (hf : T.NN f) (hv : T.NN u) :
    T.Le (fun i p => f i p * u i p) (fun i p => g i p * v i p) := by
  have g0 := nn_of_le h hf
  obtain ⟨C,hC,b,h⟩ := h
  obtain ⟨D,hD,c,h'⟩ := h'
  refine ⟨C*D, mul_pos hC hD, b+c, fun i p hx => ?_⟩
  calc
    _ ≤ _ := mul_le_mul (h i p hx) (h' i p hx) (hv i p hx) (mul_nonneg (mul_nonneg hC.le (pow_nonneg (T.cheap_pos hx).le _)) (g0 i p hx))
    _ = _ := by rw [pow_add]; ring

lemma Le.add (h : T.Le f g) (h' : T.Le u g) (hg : T.NN g) :
    T.Le (fun i p => f i p + u i p) g := by
  obtain ⟨C,hC,b,h⟩ := h
  obtain ⟨D,hD,c,h'⟩ := h'
  refine ⟨C+D, add_pos hC hD, b ⊔ c, fun i p hx => ?_⟩
  specialize hg i p hx; dsimp only
  rw [add_mul,add_mul]
  apply add_le_add ((h i p hx).trans ?_) ((h' i p hx).trans ?_) <;>
    (gcongr <;> first | exact T.one_le i p hx | simp)

lemma Le.finset_sum (s : Finset α) {f : α → ι → E → ℝ} (h : ∀ a ∈ s, T.Le (f a) g)
    (hg : T.NN g) : T.Le (fun i p => ∑ a ∈ s, f a i p) g := by
  classical
  induction s using Finset.induction with
  | empty => exact of_le (fun i p hx => by simpa using hg i p hx)
  | insert a s ha IH =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (IH (fun j hj => h j (Finset.mem_insert_of_mem hj))) hg

lemma Le.const_mul (h : T.Le f g) (c : ℝ) (hc : 0 ≤ c) (hg : T.NN g) :
    T.Le (fun i p => c*f i p) g := by
  obtain ⟨C,hC,b,h⟩ := h
  refine ⟨(c+1)*C, by positivity, b, fun i p hx => ?_⟩
  have hm := (T.cheap_pos hx).le; have hg := hg i p hx
  calc
    c * _ ≤ _ := mul_le_mul_of_nonneg_left (h i p hx) hc
    _ ≤ (c+1)*(C * T.cheap i p ^ b*g i p) := by gcongr; linarith
    _ = _ := by ring

lemma Le.cancel (h : T.Le f g) (hw : T.NN w) : T.Le (fun i p => f i p*w i p) (fun i p => g i p*w i p) := by
  obtain ⟨C,hC,b,h⟩ := h
  refine ⟨C,hC,b, fun i p hx => ?_⟩
  simpa only [← mul_assoc] using mul_le_mul_of_nonneg_right (h i p hx) (hw i p hx)

lemma Le.pow (h : T.Le f g) (hf : T.NN f) (k : ℕ) : T.Le (fun i p => f i p^k) (fun i p => g i p^k) := by
  induction k with
  | zero => exact of_le fun _ _ _ => by simp
  | succ k ih => simpa [pow_succ] using ih.mul h (fun i p hx => pow_nonneg (hf i p hx) _) hf

lemma Le.pull {S : Cost ι' F} (h : T.Le f g)
    {φ : ι' → ι} {ψ : ι' → F → E}
    (hp : ∀ i, MapsTo (ψ i) (S.zone i) (T.zone (φ i)))
    (hc : S.Le (fun i p => T.cheap (φ i) (ψ i p)) (fun _ _ => 1)) (hg : T.NN g) :
    S.Le (fun i p => f (φ i) (ψ i p)) (fun i p => g (φ i) (ψ i p)) := by
  obtain ⟨C,hC,b,h⟩ := h; obtain ⟨D,hD,c,hc⟩ := hc
  refine ⟨C*D^b, by positivity, c*b, fun i p hx => ?_⟩
  have hn := hp i hx; have ht := (S.cheap_pos hx).le
  apply (h _ _ hn).trans
  have hγ := T.one_le _ _ hn; have hm : 0≤ T.cheap _ _ := zero_le_one.trans hγ
  refine mul_le_mul_of_nonneg_right ?_ (hg _ _ hn)
  calc
    C * _ ^ b ≤ C * (D*S.cheap i p ^ c)^b := by
      have ht : T.cheap (φ i) (ψ i p) ≤ D*S.cheap i p ^ c := by simpa using hc i p hx
      gcongr
    _ = _ := by rw [mul_pow,pow_mul,mul_assoc]

end Cost
end YM.MS
