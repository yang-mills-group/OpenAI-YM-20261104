import YangMills.WilsonProof.NativeSupport.Commissioned259.Crop
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-! # Price bookkeeping also used for the first line of M.2 (comparison with physical
measurements).

Prove a slightly general form of the finite crop estimate onto the mapping (`K`, in the
application) with costs. Arbitrary weights. Thus the reader can use cancellation of T^W on
products before raising the order and invert. Use filters only for *uniform* eventual bounds
(see later de-filtering of the comparisons).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259
namespace Comparing
open Function Filter Set PowerSeries Asymptotics MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {I J E : Type*} [Norm E] {X : Filter I} {u v w T g : I → ℝ}

def logs (T : I → ℝ) (i : I) := 1 + Real.log (T i)
def Fare (T : I → ℝ) (X : Filter I) (u : I → ℝ) (f : I → E) :=
  ∃ p : ℕ, f =O[X] (fun i => u i * logs T i ^ p)
namespace Fare
section
variable {f : I → E}
lemma bare (h : f =O[X] u) : Fare T X u f := ⟨0, by simpa only [pow_zero,mul_one]⟩
lemma of_le (n : ℕ) (C : ℝ) (hC : 0 ≤ C) (h : ∀ᶠ i in X, ‖f i‖ ≤ C * (u i * logs T i ^ n)) : Fare T X u f := by
  refine ⟨n,IsBigO.of_bound C (h.mono fun i hi=>hi.trans ?_)⟩
  rw [Real.norm_eq_abs]; gcongr; exact le_abs_self _
lemma congr (h : Fare T X u f) {f' : I → E} (hf : ∀ᶠ i in X, f i=f' i) : Fare T X u f' := by
  obtain ⟨p,h⟩ := h; exact ⟨p,h.congr' hf (EventuallyEq.refl ..)⟩
lemma extend (h : Fare T X u f) (H : ∀ᶠ i in X, u i = v i) : Fare T X v f := by
  obtain ⟨p,h⟩ := h; exact ⟨p,h.congr' (EventuallyEq.refl ..) (H.mono fun i hi=> by dsimp only; rw [hi])⟩
lemma comp {ι : Type*} {Y : Filter ι} {k : ι→I} (h : Fare T X u f) (H : Tendsto k Y X) :
    Fare (T ∘ k) Y (u ∘ k) (f ∘ k) := by
  obtain ⟨p,h⟩ := h; exact ⟨ p,h.comp_tendsto H ⟩
lemma transport (h : Fare T X u f) (H : u =O[X] v) : Fare T X v f := by
  obtain ⟨p,h⟩ := h; exact ⟨ p,h.trans (H.mul (isBigO_refl (fun i=> logs T i ^ p) X))⟩
lemma log_price (hT : ∀ᶠ i in X, 1 ≤ T i) : ∀ᶠ i in X, 1 ≤ logs T i := hT.mono fun i h=> by
  unfold logs; linarith only [Real.log_nonneg h]
lemma longer (hT : ∀ᶠ i in X, 1 ≤ T i) {p q : ℕ} (hq : p ≤ q) (h : f =O[X] (fun i => u i * logs T i ^ p)) :
    f =O[X] (fun i => u i * logs T i ^ q) := by
  refine h.trans (IsBigO.of_bound' ?_)
  filter_upwards [log_price hT] with i hi
  simp only [norm_mul,norm_pow]
  gcongr; exact hi.trans (le_abs_self _)
end
-- override E when stronger structure needed
lemma pays {E : Type*} [SeminormedAddCommGroup E] {f : I→E} (hT : ∀ᶠ i in X, 1 ≤ T i)
    (H : ∀ᶠ i in X, 0 ≤ u i) (h : Fare T X u f) :
    ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∀ᶠ i in X, ‖f i‖ ≤ C*u i*(logs T i)^p := by
  obtain ⟨p,h⟩ := h; obtain ⟨C,hC,h⟩ := h.exists_pos; refine ⟨C,hC,p,?_⟩
  filter_upwards [h.bound,H,log_price hT] with i h H L
  rw [mul_assoc]; exact h.trans_eq (congr_arg (C * ·) (Real.norm_of_nonneg (by positivity)))

variable {E : Type*} [NormedAddCommGroup E] {f g' : I → E}

lemma nil (w : I → ℝ) : Fare T X w (fun i : I => (0:E)) := bare (isBigO_zero ..)
lemma neg (h : Fare T X u f) : Fare T X u (fun i => - f i) := by
  obtain ⟨p,h⟩:= h; exact ⟨p,(isBigO_neg_left).mpr h⟩
lemma add (hT : ∀ᶠ i in X, 1 ≤ T i) (hf : Fare T X u f) (hg : Fare T X u g') : Fare T X u (fun i=> f i + g' i) := by
  obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
  exact ⟨max p q, (longer hT (le_max_left ..) hp).add (longer hT (le_max_right ..) hq)⟩
lemma sub (hT : ∀ᶠ i in X, 1 ≤ T i) (hf : Fare T X u f) (hg : Fare T X u g') : Fare T X u (fun i=> f i - g' i) := by
  simp_rw [sub_eq_add_neg]; exact add hT hf hg.neg

lemma sum (hT : ∀ᶠ i in X, 1 ≤ T i) {s : Finset J} {f : J → I → E}
    (hf : ∀ j∈s, Fare T X u (f j)) : Fare T X u (fun i=>∑ j ∈ s, f j i) := by
  induction s using Finset.induction_on with
  | empty => simp_rw [Finset.sum_empty]; exact nil _
  | insert j s hj ih => simp_rw [Finset.sum_insert hj]; exact add hT (hf j (Finset.mem_insert_self ..)) (ih fun j hj=>hf j (Finset.mem_insert_of_mem hj))

variable {K : Type*} [NormedRing K] {A B C D : I → K}

lemma constant (x : K) : Fare T X (fun _=>1) (fun _=>x) := bare (IsBigO.of_bound ‖x‖ (Eventually.of_forall fun i=>by simp))
lemma cent {x : ℝ} (h : ∀ᶠ i in X, ‖A i‖ ≤ x) : Fare T X (fun _ => 1) A :=
  bare (IsBigO.of_bound x (by simpa only [norm_one,mul_one] using h))
lemma mul (h : Fare T X u A) (hp : Fare T X v B) : Fare T X (fun i=>u i*v i) (fun i=>A i*B i) := by
  obtain ⟨p,hp'⟩ := h; obtain ⟨q,hq⟩:=hp; exact ⟨p+q,(hp'.mul hq).congr_right (fun i=>by rw [pow_add]; ring)⟩
lemma cover (h : Fare T X (fun _=>1) A) (hp : Fare T X u B) : Fare T X u (fun i=>A i*B i) := by
  simpa only [one_mul] using h.mul hp
lemma budget (hT : ∀ᶠ i in X, 1 ≤ T i) (hf : Fare T X u A) (_hg : Fare T X v B)
    (hc : Fare T X v D) (ha : Fare T X (fun i=>g i * u i) (fun i=> A i-C i))
    (hb : Fare T X (fun i=>g i * v i) (fun i=> B i-D i)) :
    Fare T X (fun i=>g i*(u i*v i)) (fun i=> A i * B i - C i * D i) := by
  have hx := ha.mul hc; have hy:= hf.mul hb
  refine (Fare.add hT (hy.extend ?_) (hx.extend ?_)).congr ?_
  exact Eventually.of_forall fun i=>by ring
  exact Eventually.of_forall fun i=>by ring
  exact Eventually.of_forall fun i=>by rw [sub_mul,mul_sub]; abel

section
variable {A B : J → I → ℂ} {u : J → I → ℝ}
lemma prod {s : Finset J} (hf : ∀ j ∈ s,Fare T X (u j) (A j)) :
    Fare T X (fun i=>∏ j∈s,u j i) (fun i=>∏ j∈s,A j i) := by
  induction s using Finset.induction_on with
  | empty => simp_rw [Finset.prod_empty]; exact constant _
  | insert j s hj ih => simp_rw [Finset.prod_insert hj]; exact (hf j (Finset.mem_insert_self ..)).mul (ih fun j hj=>hf j (Finset.mem_insert_of_mem hj))
lemma overall (hT : ∀ᶠ i in X, 1 ≤ T i) {s : Finset J} (hf : ∀ j ∈ s,Fare T X (u j) (A j))
    (hg : ∀ j ∈ s,Fare T X (u j) (B j)) (he : ∀ j ∈ s, Fare T X (fun i=>g i*u j i) (fun i=> A j i - B j i)) :
    Fare T X (fun i=>g i * (∏ j∈s,u j i)) (fun i=>(∏ j∈s,A j i)-(∏ j∈s,B j i)) := by
  induction s using Finset.induction_on with
  | empty => simp_rw [Finset.prod_empty, sub_self]; exact nil _
  | insert k s hk ih =>
    simp_rw [Finset.prod_insert hk]; refine budget hT (hf k (Finset.mem_insert_self ..))
      (prod (fun i hi=>hf i (Finset.mem_insert_of_mem hi))) (prod (fun i hi=>hg i (Finset.mem_insert_of_mem hi)))
      (he k (Finset.mem_insert_self ..)) (ih ?_ ?_ ?_)
    all_goals intro i hi; first | exact he i (Finset.mem_insert_of_mem hi)|exact hf i (Finset.mem_insert_of_mem hi)|exact hg i (Finset.mem_insert_of_mem hi)
end
lemma zero_pow (h : Fare T X (fun _=>1) A) (n : ℕ) : Fare T X (fun _ => 1) (fun i=> A i ^ n) := by
  induction n with
  | zero => simp_rw [pow_zero]; exact constant _
  | succ k ih => simp_rw [pow_succ]; exact cover ih h
lemma over_pow (n m : ℕ) (h : n ≤ m) (X : Filter I) (g : I → ℝ) (ht : ∀ᶠ i in X, |g i| ≤ 1) :
    (fun i=> g i ^ m) =O[X] (fun i=> g i ^ n) := by
  refine IsBigO.of_bound' ?_
  filter_upwards [ht] with i hi
  rw [norm_pow,norm_pow]; exact pow_le_pow_of_le_one (norm_nonneg _) hi h
end Fare
end Comparing
end YM.FVA2.GradedFar259
