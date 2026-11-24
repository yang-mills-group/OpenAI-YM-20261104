import YangMills.WilsonProof.NativeSupport.Commissioned259.ScaleCost.Crop
/-! # Price algebra shared by QScale & later moving estimates

Local `m`: at this hypothesis a cost through exactly perturbative order m,
`f` the book entry, NOT cropping implicitly before operations. These package our proved crop
estimates (not assumptions).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Quotes
open Function Filter Set PowerSeries Asymptotics
open XSpace XSpace.Normalize XSpace.Structure1
open Scale O.Score O.Enh Comparing
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {I J E:Type*} [Norm E] {L:Filter I} {m:ℕ}
    {w w' t v T g : I → ℝ} (pay : t=O[L] g)
    (ht : ∀ᶠ i in L, |t i| ≤ 1) (hg : ∀ᶠ i in L, |g i| ≤ 1)
    (hT : ∀ᶠ i in L, 1≤T i)

/-- Q-scale compact takes T=1 here, moving windows use the log allowed. -/
structure Coin (L:Filter I) (T t g : I→ℝ) (m:ℕ) (w:I→ℝ) (X:I→ℂ) (F:I→PowerSeries ℂ) : Prop where
    prices : Tunes T L w F
    expense : Fare T L (fun i=>g i^(m+1)*w i) (fun i=> X i - crop m (t i) (F i))
namespace Coin
variable {A B D : I→ℂ} {F Q : I→ PowerSeries ℂ}

lemma adjust {u : I→ℝ} (h:Coin L T t g m w A F) (hp:w=O[L] u) : Coin L T t g m u A F :=
  ⟨fun n=>(h.prices n).transport hp,h.expense.transport ((isBigO_refl (fun i=>g i^(m+1)) L).mul hp)⟩
lemma congr (h:Coin L T t g m w A F) (e : ∀ᶠ i in L, A i=B i) (u : ∀ᶠ i in L,F i=Q i) (v : ∀ᶠ i in L, w i=w' i) : Coin L T t g m w' B Q := by
  refine ⟨ fun i=> ((h.prices i).congr (u.mono ?_)).extend v, (h.expense.congr ((e.and u).mono ?_)).extend (v.mono ?_) ⟩
  · intro i hi; rw [hi]
  · intro i hi; rw [hi.1,hi.2]
  intro i hi; rw [hi]
lemma sumzero (w : I→ℝ) : Coin L T t g m w (fun _=>0) (fun _=>0) := by
  refine ⟨fun i=>?_,?_⟩
  · simp_rw [_root_.map_zero]; exact Fare.nil _
  simp_rw [_root_.map_zero,sub_self]; exact Fare.nil _
lemma already (h: Tunes T L w F) : Coin L T t g m w (fun i=>crop m (t i) (F i)) F := by
  refine ⟨h,?_⟩; simp_rw [sub_self]; exact Fare.nil _
lemma literal (z:I→ℂ) (h:Fare T L w z) : Coin L T t g m w z (fun i=>C (z i)) := by
  have hz i : crop m (t i) (C (z i))=z i := by
    rw [crop_apply,Finset.sum_eq_single 0]
    · simp
    · intro k _ hk; rw [coeff_C,if_neg hk,mul_zero]
    simp
  refine ⟨ fun i=>?_,?_⟩
  · simp_rw [coeff_C]; by_cases hp:i=0;
    · simp_rw [if_pos hp]; exact h
    simp_rw [if_neg hp]; exact Fare.nil _
  simp_rw [hz,sub_self]; exact Fare.nil _
include hT
lemma add (h:Coin L T t g m w A F) (q:Coin L T t g m w B Q) : Coin L T t g m w (fun i=>A i+B i) (fun i=>F i+Q i) := by
  refine ⟨Tunes.add hT h.prices q.prices,(Fare.add hT h.expense q.expense).congr (Eventually.of_forall fun i=>?_)⟩
  rw [map_add]; abel
lemma sum {s:Finset J} {A:J→I→ℂ} {F:J→I→PowerSeries ℂ} (h:∀ i∈s,Coin L T t g m w (A i) (F i)) :
    Coin L T t g m w (fun k=>∑ i∈s,A i k) (fun k=>∑ i∈s,F i k) := by
  induction s using Finset.induction_on generalizing A F with
  | empty=> simp_rw [Finset.sum_empty]; exact sumzero _
  | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact add hT (h i (Finset.mem_insert_self ..)) (ih fun i e=> h i (Finset.mem_insert_of_mem e))

include ht hg
lemma small (m:ℕ) (h:Fare T L (fun i=>g i^(m+1)*w i) A) : Fare T L w A := by
  refine h.transport (IsBigO.of_bound' ?_); filter_upwards [hg] with i hi; rw [norm_mul,norm_pow]; exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hi)
lemma costs (h:Coin L T t g m w A F) : Fare T L w A := by
  refine (Fare.add hT (small ht hg hT m h.expense) (Tunes.cuts hT ht m h.prices)).congr (Eventually.of_forall fun i=>?_)
  simp

include pay
lemma mul (h:Coin L T t g m w A F) (q:Coin L T t g m w' B Q) : Coin L T t g m (fun i=>w i*w' i) (fun i=>A i*B i) (fun i=>F i*Q i) := by
  refine ⟨Tunes.mix hT h.prices q.prices,?_⟩
  have Y:= Tunes.cuts hT ht m q.prices
  exact (Fare.add hT (Fare.budget hT (costs ht hg hT h) (costs ht hg hT q) Y h.expense q.expense) (Tunes.overflow hT ht pay m h.prices q.prices)).congr (Eventually.of_forall fun i=> sub_add_sub_cancel ..)
lemma prod {A:J→I→ℂ}{F:J→I→PowerSeries ℂ}(s:Finset J)(w:J→I→ℝ)(h:∀ i∈s,Coin L T t g m (w i) (A i) (F i)) :
    Coin L T t g m (fun k=>∏ i∈s,w i k) (fun k=>∏ i∈s,A i k) (fun k=>∏ i∈s,F i k) := by
  induction s using Finset.induction_on with
  | empty=> simp_rw [Finset.prod_empty]; exact (literal _ (Fare.constant 1)).congr (EventuallyEq.refl ..) (Eventually.of_forall fun i=>map_one C) (EventuallyEq.refl ..)
  | insert j s hj ih=> simp_rw [Finset.prod_insert hj]; exact mul pay ht hg hT (h j (Finset.mem_insert_self ..)) (ih fun i e=>h i (Finset.mem_insert_of_mem e))

-- The frame trials and (F4) & (G9) proofs use CONCRETE substitution, point costs before
-- cropping. `g` in same units BOTH sides already (pay by actual order estimate if meter differs).
omit hg
lemma substitute {v:I→ℝ} (hv:∀ᶠ i in L, |v i| ≤ 1) (k:Coin L T t g m (fun _=>1) (fun i=>(v i:ℂ)) Q) (a:∀ i, MS.Book.Program.Rooted (Q i))
    (f : Coin L T v g m w A F) : Coin L T t g m w A (fun i=> (F i).subst (Q i)) :=
  ⟨ ScaleCost.submitted hT k.prices f.prices a, (Fare.add hT f.expense (ScaleCost.clock_inserting hT ht pay k.prices f.prices a m hv (by simpa only [mul_one] using k.expense))).congr (Eventually.of_forall fun i=> sub_add_sub_cancel .. ) ⟩
omit ht pay
lemma covered (h:Coin L T t g m w A F) (e:Fare T L (fun i=>g i^(m+1)*w i) (fun i=>B i-A i)) : Coin L T t g m w B F :=
  ⟨ h.prices, (Fare.add hT e h.expense).congr (Eventually.of_forall fun i=> sub_add_sub_cancel ..) ⟩
lemma quick {s:I→ℝ} (Q:Coin L T t s m w A F)(u:s=O[L] g) : Coin L T t g m w A F :=
  ⟨ Q.prices, Q.expense.transport ((u.pow _).mul (isBigO_refl w L))⟩
end Coin
end YM.FVA2.GradedFar259.Quotes
