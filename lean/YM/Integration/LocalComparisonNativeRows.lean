import YM.Integration.LocalComparisonReadout
import YM.Integration.OverlayFiniteRegular
import YM.Integration.OverlayForcedBarcode

/-!
The common coefficient envelopes in the local-comparison norm are native
row payments on the same presentation.  The factor below counts only the
fixed local marker type.  There is no sum over lattice sites or test choices.
Captions remain unmasked, and the forced rows retain the original quiet K.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay
open RG3.Forms RG3.Script.Picnic MergeProof MergeProof.Accent Push.AbsoluteSums
open scoped BigOperators Classical

private theorem hit_of_global {I : Type*} {n : Side} {s : I → Support n}
    {a : I → ℝ} {p : BudgetPoint} {c : ℝ} (ha : ∀ i, 0 ≤ a i)
    (h : SumBudget (fun i => p.mass (s i) (a i)) c) :
    Ac.Hit s p.B a p.supportExponent c := by
  intro z
  apply budget_mono h
  · intro i
    split_ifs
    · exact mul_nonneg (ha i) (Real.exp_pos _).le
    · rfl
  · intro i
    split_ifs
    · simpa only [BudgetPoint.mass, mul_comm] using (le_refl (a i * Real.exp (p.supportExponent * coverNumber p.B (s i))))
    · exact (ha i).trans (p.loMass _ _ (ha i))

private theorem rows_of_global {I Y V : Type*} [DecidableEq V]
    {R : Census V} {n : Side} {p : BudgetPoint} {w : V → ℝ}
    {s : I → Support n} {mode : I → R.Mode} {f : I → Y → ℂ}
    {b : I → ℝ} {c : ℝ} (hw : ∀ v, 0 < w v) (hb : ∀ i, 0 ≤ b i)
    (hf : ∀ i y, ‖f i y‖ ≤ b i)
    (h : SumBudget (fun i => Poly.toll w (mode i) * p.mass (s i) (b i)) c) :
    Towed w s (fun i y => Poly.send (mode i) (f i y)) p.B p.supportExponent c := by
  let a i := Poly.toll w (mode i) * b i
  have ha i : 0 ≤ a i := mul_nonneg (Poly.worth hw _).le (hb i)
  have hm : SumBudget (fun i => p.mass (s i) (a i)) c := by
    convert h using 1
    funext i
    dsimp [a, BudgetPoint.mass]
    ring
  refine ⟨a, hm.2.1.of_nonneg_of_le ha (fun i => p.loMass _ _ (ha i)),
    hit_of_global ha hm, ?_⟩
  intro i
  exact satin (f i) (mode i) (b i) (hb i) (hf i)

private theorem towed_add {I Y V : Type*} [DecidableEq V] {R : Census V}
    {n : Side} {w : V → ℝ} {s : I → Support n}
    {F H : I → Y → Poly R} {M : ℕ} {e a b : ℝ}
    (hF : Towed w s F M e a) (hH : Towed w s H M e b) :
    Towed w s (fun i y => F i y + H i y) M e (a + b) := by
  obtain ⟨f, hf, hHitF, hLociF⟩ := hF
  obtain ⟨g, hg, hHitG, hLociG⟩ := hH
  refine ⟨fun i => f i + g i, hf.add hg, ?_, ?_⟩
  · intro z
    convert Extra.Multi.Budget.plus (hHitF z) (hHitG z) using 1
    funext i
    split_ifs <;> ring
  · intro i
    obtain ⟨v, hv, hV, hpV⟩ := hLociF i
    obtain ⟨z, hz, hZ, hpZ⟩ := hLociG i
    refine ⟨fun q => v q + z q, fun q => add_nonneg (hv q) (hz q), ?_, ?_⟩
    · intro y q
      exact (norm_add_le _ _).trans (add_le_add (hV y q) (hZ y q))
    · simpa only [Push.GridApprox.Nil.wordsPrice, mul_add, sum_add_distrib]
        using add_le_add hpV hpZ

private theorem tally_fst {Y V : Type*} [DecidableEq V] {R : Census V}
    (F : ℕ × ℕ → Y → Poly R) (i : ℕ) (y : Y) :
    tally Prod.fst F i y = ∑' j, F (i, j) y := by
  let e : ℕ ≃ {q : ℕ × ℕ // q.1 = i} := {
    toFun := fun j => ⟨(i, j), rfl⟩
    invFun := fun q => q.val.2
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨⟨k, j⟩, h⟩
      cases h
      rfl }
  exact (e.tsum_eq (fun q => F q.val y)).symm

variable {G : Gauge} {n : Side} {V : Type} {X : Type*}
    [Fintype V] [DecidableEq V] {R : Census V} {P : Rep G n}
    {o : V → Site n} {T : Taste X o P R} {p : BudgetPoint}
    {w : V → ℝ} {κ regularPrice forcedPrice : ℝ}

/-- The same literal masked regular rays and unmasked captions have common
native payments. The unit channel is retained in the final total. -/
theorem FullBudget.native_regular
    (h : FullBudget p T w κ regularPrice forcedPrice)
    (hthreshold : p.threshold = P.p.threshold) (x₀ : X) :
    ∃ b d : ℝ, 0 ≤ b ∧ 0 ≤ d ∧
      Towed w T.menu.branch
        (fun i (z : X × Config G n) => (T.leaf z.1).contents.ray i z.2)
        p.B p.supportExponent b ∧
      Towed w T.site
        (fun i (z : X × Config G n) => Poly.send (T.tag i) (T.score z.1 i))
        p.B p.supportExponent d ∧
      (∑ v, w v * h.unitBound v) + b + d ≤ Fintype.card V * regularPrice := by
  choose B D hB hD htotal using h.regularTotal
  have hr : SumBudget
      (fun i => Poly.toll w (T.menu.rays i) * p.mass (T.menu.branch i) (h.white i))
      (∑ v, B v) := rooted_sumBudget
    (fun i => mul_nonneg (Poly.worth h.radii _).le
      ((h.white_nonnegative i).trans (p.loMass _ _ (h.white_nonnegative i))))
    (fun i => (h.active x₀).articles.proper i) hB
  have hc : SumBudget
      (fun i => Poly.toll w (T.tag i) * p.mass (T.site i) (h.gold i))
      (∑ v, D v) := rooted_sumBudget
    (fun i => mul_nonneg (Poly.worth h.radii _).le
      ((h.gold_nonnegative i).trans (p.loMass _ _ (h.gold_nonnegative i))))
    (fun i => (h.active x₀).captions.card i) hD
  refine ⟨∑ v, B v, ∑ v, D v,
    (tsum_nonneg hr.1).trans hr.2.2, (tsum_nonneg hc.1).trans hc.2.2, ?_, ?_, ?_⟩
  · apply rows_of_global h.radii h.white_nonnegative ?_ hr
    intro i z
    change ‖masked P.p.threshold (T.menu.branch i) (T.menu.regular z.1 i) z.2‖ ≤ _
    by_cases hU : Healthy P.p.threshold (T.menu.branch i) z.2
    · rw [masked_eq _ _ _ _ hU]
      obtain ⟨v, hv⟩ := (h.active z.1).articles.proper i
      exact grain_value ((h.regular i).controls z.1 v hv) z.2 (hthreshold.symm ▸ hU)
    · rw [masked_ne _ _ _ _ hU, norm_zero]
      exact h.white_nonnegative i
  · exact rows_of_global h.radii h.gold_nonnegative (fun i z => h.caption z.1 i) hc
  · rw [← sum_add_distrib, ← sum_add_distrib]
    exact (sum_le_sum (fun v _ => htotal v)).trans_eq (by simp)

/-- Original marked forced addresses receive a single envelope before all
independent tests and fields, without changing the cover exponent. -/
theorem FullBudget.native_marked
    (h : FullBudget p T w κ regularPrice forcedPrice) (x₀ : X) :
    Towed w (fun i : ℕ × ℕ => (P.activities.forced i.1).support)
      (fun i (z : X × Config G n) => (T.leaf z.1).contents.tagged i.1 i.2 z.2)
      p.B p.supportExponent (Fintype.card V * (κ * forcedPrice)) := by
  apply rows_of_global (p := p)
    (s := fun i : ℕ × ℕ => (P.activities.forced i.1).support)
    (mode := fun i : ℕ × ℕ => T.menu.marks i.1 i.2)
    (f := fun (i : ℕ × ℕ) (z : X × Config G n) => T.menu.force z.1 i.1 i.2 z.2)
    h.radii h.black_nonnegative
    (fun (i : ℕ × ℕ) (z : X × Config G n) => h.forced z.1 i.1 i.2 z.2)
  have ht := rooted_sumBudget
    (fun i : ℕ × ℕ => mul_nonneg (Poly.worth h.radii _).le
      ((h.black_nonnegative i).trans (p.loMass _ _ (h.black_nonnegative i))))
    (fun i : ℕ × ℕ => (h.active x₀).articles.occurs i.1 i.2) h.forcedTotal
  simpa using ht

omit [Fintype V] in
/-- The original quiet K uses its own native reserve. This is a common
payment over the test parameter even though K itself does not vary. -/
theorem native_quiet (hK : P.activities.KBound p κ) :
    Towed w (fun i => (P.activities.forced i).support)
      (fun i (z : X × Config G n) => Poly.send R.quiet (P.activities.K i z.2 : ℂ))
      p.B p.supportExponent κ := by
  obtain ⟨b, hb, hHit⟩ := hK
  refine ⟨b, Activities.summable_charge
    (fun i => (P.activities.forced i).inventory_ne.mono
      (P.activities.forced i).inventory_sup) (fun i => (hb i).1) hHit, ?_, ?_⟩
  · intro z
    convert hHit z using 1
    funext i
    unfold BudgetPoint.mass
    split_ifs <;> ring
  · intro i
    have ht := satin (w := w) (fun z : X × Config G n => (P.activities.K i z.2 : ℂ))
      R.quiet (b i) (hb i).1
      (fun z => by simpa only [Complex.norm_real] using (hb i).2 z.2)
    simpa only [Poly.quiet_toll, one_mul] using ht

/-- Complete forced rows, including quiet K, retain the original countable
address sum. The test parameter is inside the one common native envelope. -/
theorem FullBudget.native_each
    (h : FullBudget p T w κ regularPrice forcedPrice)
    {quietPrice : ℝ} (hK : P.activities.KBound p quietPrice) (x₀ : X) :
    Towed w (fun i => (P.activities.forced i).support)
      (fun i (z : X × Config G n) => (T.leaf z.1).contents.each i z.2)
      p.B p.supportExponent (quietPrice + Fintype.card V * (κ * forcedPrice)) := by
  have hm := towing (r := fun i : ℕ => (P.activities.forced i).support)
    Prod.fst (fun i (z : X × Config G n) => (T.leaf z.1).contents.tagged i.1 i.2 z.2)
    (h.native_marked x₀) h.radii
  have hm' : Towed w (fun i => (P.activities.forced i).support)
      (fun i (z : X × Config G n) => ∑' j, (T.leaf z.1).contents.tagged i j z.2)
      p.B p.supportExponent (Fintype.card V * (κ * forcedPrice)) := by
    convert hm using 1
    funext i z
    exact (tally_fst (R := R)
      (fun i (z : X × Config G n) => (T.leaf z.1).contents.tagged i.1 i.2 z.2) i z).symm
  exact towed_add (native_quiet hK) hm'

/-- Native barcode aggregation keeps every original forced address and its
multiplicity. No representation equality is an additional hypothesis. -/
theorem FullBudget.native_full_forced
    (h : FullBudget p T w κ regularPrice forcedPrice)
    {quietPrice : ℝ} (hK : P.activities.KBound p quietPrice) (x₀ : X) :
    Towed w Prod.fst
      (fun box (z : X × Config G n) => OverlayForcedBarcode.full (T.leaf z.1).contents box z.2)
      p.B p.supportExponent (quietPrice + Fintype.card V * (κ * forcedPrice)) :=
  towing (barcode P.activities)
    (fun i (z : X × Config G n) => (T.leaf z.1).contents.each i z.2)
    (h.native_each hK x₀) h.radii

end YM.Integration.LocalComparison
