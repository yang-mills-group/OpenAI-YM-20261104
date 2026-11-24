import YangMills.WilsonProof.NativeSupport.Commissioned259.Compare.Currency
/-!
# Estimate also composition tail (over all Far fields vs exact reports)
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Comparing
open Function Filter Set PowerSeries Asymptotics MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {I J : Type*} {T t u v w g : I → ℝ} {X : Filter I} (hT : ∀ᶠ i in X, 1 ≤ T i)
variable (ht : ∀ᶠ i in X, |t i| ≤ 1) (hw : t=O[X] g)

abbrev Tunes (T : I → ℝ) (X : Filter I) (w : I → ℝ) (A : I → PowerSeries ℂ) := ∀ n : ℕ,
  Fare T X w (fun i => coeff n (A i))
namespace Tunes
variable {A B : I → PowerSeries ℂ}
include hT
lemma add (h : Tunes T X u A) (H : Tunes T X u B) : Tunes T X u (fun i => A i+B i) := by
  intro n; simp_rw [map_add]; exact Fare.add hT (h n) (H n)
lemma sum (F : J → I → PowerSeries ℂ) (s : Finset J) (H : ∀ j∈s, Tunes T X u (F j)) : Tunes T X u (fun i=>∑ j∈s,F j i) := by
  intro n; simp_rw [map_sum]; exact Fare.sum hT fun j hj=> H j hj n
lemma mix (h : Tunes T X u A) (H : Tunes T X v B) : Tunes T X (fun i=>u i*v i) (fun i=> A i * B i) := by
  intro n; simp_rw [coeff_mul]; exact Fare.sum hT fun j hj=> (h j.1).mul (H j.2)
lemma bill (F : J → I → PowerSeries ℂ) (U : J → I→ℝ) (s : Finset J) (H : ∀ j∈s, Tunes T X (U j) (F j)) : Tunes T X (fun i=>∏ j∈s,U j i) (fun i=>∏ j∈s,F j i) := by
  induction s using Finset.induction_on with
  | empty=> simp_rw [Finset.prod_empty]; exact fun n=>Fare.constant _
  | insert j s hj ih => simp_rw [Finset.prod_insert hj]; exact mix hT (H j (Finset.mem_insert_self ..)) (ih fun j hj=> H j (Finset.mem_insert_of_mem hj))
include ht
omit hT in
lemma budget_b (n : ℕ) : Fare T X (fun _=>1) (fun i => (t i:ℂ)^n) := Fare.zero_pow
  (Fare.cent (ht.mono (p:=fun i=> |t i| ≤ 1) fun i hi=> show ‖(t i:ℂ)‖ ≤ 1 from by simpa [Real.norm_eq_abs] using hi)) _

include hw
omit hT in
lemma budget_P (n k : ℕ) (hn : k≤n) : Fare T X (fun i=>g i^k) (fun i=>(t i:ℂ)^n) := by
  refine Fare.bare (isBigO_norm_left.mp ?_)
  have H:= isBigO_norm_left.mpr ((Fare.over_pow k n hn X t ht).trans (hw.pow k))
  simpa only [norm_pow, Complex.norm_real] using H

omit hw in
lemma cuts (p : ℕ) (h : Tunes T X u A) : Fare T X u (fun i=> crop p (t i) (A i)) := by
  simp_rw [crop_apply]; exact Fare.sum hT fun i _=>Fare.cover (budget_b ht i) (h i)
lemma excess (q p : ℕ) (hq : p≤q) (h : Tunes T X u A) : Fare T X (fun i=> g i^(p+1)*u i) (fun i=> crop q (t i) (A i)-crop p (t i) (A i)) := by
  induction q, hq using Nat.le_induction with
  | base => simp_rw [sub_self]; exact Fare.nil _
  | succ j hj ih =>
    have H : ∀ i, crop (j+1) (t i) (A i)-crop p (t i) (A i)=
        crop j (t i) (A i)-crop p (t i) (A i)+(t i:ℂ)^(j+1)*coeff (j+1) (A i) := fun i=>by
      simp_rw [crop_apply]; rw [Finset.sum_range_succ]; abel
    simp_rw [H]; exact Fare.add hT ih ((budget_P ht hw (j+1) (p+1) (by omega)).mul (h _))
lemma overflow (p : ℕ) (h : Tunes T X u A) (H : Tunes T X v B) : Fare T X
    (fun i=> g i^(p+1)*(u i*v i)) (fun i=> crop p (t i) (A i)*crop p (t i) (B i)-crop p (t i) (A i*B i)) := by
  simp_rw [triangle, add_sub_cancel_left]; unfold debt
  exact Fare.mul (budget_P ht hw (p+1) (p+1) le_rfl) (Fare.sum hT fun i _=> Fare.cover (budget_b ht _) ((h _).mul (H _)))
lemma late (p p' : ℕ) (h' : p ≤ p') (h : Tunes T X u A) (H : Tunes T X v B) : Fare T X (fun i=> g i^(p+1)*(u i*v i)) (fun i=> crop p' (t i) (A i)*crop p (t i) (B i)-crop p (t i) (A i*B i)) := by
  refine (Fare.add hT (((excess hT ht hw p' p h' h).mul (cuts hT ht p H)).extend ?_) (overflow hT ht hw p h H)).congr ?_
  · exact Eventually.of_forall fun i=>by rw [mul_assoc]
  exact Eventually.of_forall fun i=>by rw [sub_mul]; abel

/-- Cost of cropping *one step* vs whole inserted series. Extra head `A` (the kernel)
with crop p; consider extending the Far leg F even to any fixed later orders. -/
lemma overrun (p : ℕ) (s : Finset J) (q : J → ℕ) (hq : ∀ j∈s,p ≤ q j)
    (W : J→I→ℝ) (F : J→I→PowerSeries ℂ) (hf : ∀ j∈s, Tunes T X (W j) (F j)) (ha : Tunes T X u A) :
    Fare T X (fun i=>g i^(p+1)*((∏ j∈s,W j i)*u i)) (fun i=>
      (∏ j∈s,crop (q j) (t i) (F j i))*crop p (t i) (A i)-crop p (t i) ((∏ j∈s,F j i)*A i)) := by
  induction s using Finset.induction_on with
  | empty => simp_rw [Finset.prod_empty,one_mul,sub_self]; exact Fare.nil _
  | insert j s hj ih =>
    have h {b : J} (hb : b ∈ s) : b ∈ insert j s := Finset.mem_insert_of_mem hb
    have t₀ := Finset.mem_insert_self j s; simp_rw [Finset.prod_insert hj]
    have he:= ih (fun k hk=>hq k (h hk)) (fun k hk=>hf k (h hk))
    have H := hf j t₀; have hu := cuts hT ht (q j) H
    have H0 := late hT ht hw p (q j) (hq j t₀) H (mix hT (bill hT F W s fun j hj=>hf j (h hj)) ha)
    refine ((Fare.add hT ((hu.mul he).extend ?_) H0).congr ?_).extend ?_
    · exact Eventually.of_forall fun _=>by ring
    · refine Eventually.of_forall fun i=>?_ ; rw [mul_sub,mul_assoc _ (∏ j∈s,crop (q j) (t i) (F j i)) _,mul_assoc _ (∏ j∈s,F j i) _]; abel
    exact Eventually.of_forall fun _=>by ring
end Tunes
end YM.FVA2.GradedFar259.Comparing
