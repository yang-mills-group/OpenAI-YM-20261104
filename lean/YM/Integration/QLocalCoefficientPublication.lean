import YM.Integration.RiderTastePresentation
import YM.MergeProof.Sate
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Wind

/-! Publish scalar support-hit estimates and the full forced switch on one layout.
The regular and forced polynomial weights are summed before the physical site
budget is used. An input family is allowed when its scalar majorant is common
to all tests. The fixed-test forced specialization uses the actual `Motion.Pays`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalCoefficientPublication

open Lattice Wilson RG Marker Merge MergeProof PhysicalNext.Repeat
open Push Push.AbsoluteSums Next.Foundations RiderTastePresentation
open scoped Classical BigOperators

variable {Ω ι J V : Type} [DecidableEq V] {R : Census V} {G : Gauge} {n : Side}

/-- Keep the native region, scalar/caption selector and full forced polynomial. -/
def ledger (X : J → Support n) (total : J → Prop) (f : Ω → J → Config G n → ℝ)
    (z : J → Poly R) (forced : Ω → ℕ → Config G n → Poly R) : Ledger Ω J G n R where
  region := X
  raw x i U := (f x i U : ℂ) • z i
  total := total
  forced := forced

private theorem hit_mono {I : Type} {X : I → Support n} {M : ℕ} {α T : ℝ}
    {f g : I → ℝ} (h : Ac.Hit X M f α T) (hn : ∀ i, 0 ≤ g i)
    (hle : ∀ i, g i ≤ f i) : Ac.Hit X M g α T := by
  intro y
  apply budget_mono (h y)
  · intro i
    split
    · exact mul_nonneg (hn i) (Real.exp_nonneg _)
    · rfl
  · intro i
    split
    · exact mul_le_mul_of_nonneg_right (hle i) (Real.exp_nonneg _)
    · rfl

/-- Scale each scalar label bound by its own polynomial coefficients. The price
is allowed to vary by label, as in the 4a `pearl` bound. -/
theorem regular {p : BudgetPoint} {X : J → Support n} {α T : ℝ}
    {w : V → ℝ} (hw : ∀ v, 0 < w v) {f : Ω → J → Config G n → ℝ}
    (z : J → Poly R) (bill : J → ℝ) (hz : ∀ i, Poly.price w (z i) ≤ bill i)
    (h : ∃ b : J → ℝ, (∀ i, 0 ≤ b i) ∧
      (∀ i x, p.Regular (X i) (f x i) ∧
        ∀ y ∈ X i, p.supBounds y (X i) (f x i) (b i)) ∧
      Ac.Hit X p.B (fun i => bill i * b i) α T) :
    ∃ a : J × R.Mode → ℝ, (∀ i, 0 ≤ a i) ∧
      (∀ i q x, let F (U : Config G n) := ((f x i U : ℂ) • z i).part q
        p.Regular (X i) F ∧ ∀ y ∈ X i, p.supBounds y (X i) F (a (i,q))) ∧
      Ac.Hit X p.B (fun i => ∑ q : R.Mode, Poly.toll w q * a (i,q)) α T := by
  obtain ⟨b, hb, hf, hhit⟩ := h
  let a (i : J × R.Mode) := ‖(z i.1).part i.2‖ * b i.1
  have ha (i) : 0 ≤ a i := mul_nonneg (norm_nonneg _) (hb _)
  refine ⟨a, ha, ?_, hit_mono hhit (fun i => Finset.sum_nonneg
    fun q _ => mul_nonneg (Poly.worth hw q).le (ha _)) ?_⟩
  · intro i q x F
    have heq : F = (z i).part q • (Complex.ofReal ∘ f x i) := by
      funext U
      exact mul_comm ..
    rw [heq]
    exact ⟨regular_smul _ (Blush.ornate (hf i x).1), fun y hy =>
      bound_smul _ (Blush.pricingG (hf i x).1 ((hf i x).2 y hy))⟩
  · intro i
    dsimp only [a]
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hz i) (hb i)

/-- Protect each complete declared mark support under a common native
coefficient budget, including the quiet coefficient. -/
theorem forced_of_loci {w : V → ℝ} (hw : ∀ v, 0 < w v) (X : J → Support n)
    (M : ℕ) (F : Ω → J → Config G n → Poly R) {α W : ℝ}
    (h : ∃ b : J → ℝ, (∀ i, Accent.Loci w (fun y : Ω × Config G n => F y.1 i y.2) (b i)) ∧
      Ac.Hit X M b α W) (s : V → Support n)
    (hs : ∀ x i U q, (F x i U).part q ≠ 0 → ∀ v ∈ q.val, s v ⊆ X i) :
    ∃ a : J × R.Mode → ℝ, (∀ i, 0 ≤ a i) ∧
      (∀ i q, (∃ v ∈ q.val, ¬ s v ⊆ X i) → a (i,q) = 0) ∧
      (∀ x i U q, ‖(F x i U).part q‖ ≤ a (i,q)) ∧
      Ac.Hit X M (fun i => ∑ q : R.Mode, Poly.toll w q * a (i,q)) α W := by
  obtain ⟨b, hb, hhit⟩ := h
  choose c hc hbound hprice using hb
  let owns (i : J) (q : R.Mode) := ∀ v ∈ q.val, s v ⊆ X i
  let a (i : J × R.Mode) := if owns i.1 i.2 then c i.1 i.2 else 0
  have ha (i) : 0 ≤ a i := by
    dsimp only [a]
    split
    · exact hc _ _
    · rfl
  refine ⟨a, ha, ?_, ?_, hit_mono hhit (fun i => Finset.sum_nonneg
    fun q _ => mul_nonneg (Poly.worth hw q).le (ha _)) ?_⟩
  · rintro i q ⟨v, hv, hbad⟩
    exact if_neg (fun ho => hbad (ho v hv))
  · intro x i U q
    dsimp only [a]
    split
    · exact hbound i (x,U) q
    · rename_i ho
      rw [not_ne_iff.mp (mt (hs x i U q) ho), norm_zero]
  · intro i
    apply le_trans _ (hprice i)
    apply Finset.sum_le_sum
    intro q _
    apply mul_le_mul_of_nonneg_left _ (Poly.worth hw q).le
    dsimp only [a]
    split
    · rfl
    · exact hc _ _

/-- Full forced-polynomial majorant. The mark-address guard cuts a coefficient
only where the exact forced polynomial vanishes. The quiet mode stays in the sum. -/
theorem forced [Fintype ι] {P : Rep G n} {w : V → ℝ} {α W : ℝ}
    (hw : ∀ v, 0 < w v) (z : ι → Poly R) (hz : ∀ i, Poly.price w (z i) ≤ 1)
    (K : Ω → ℝ → Finset ι → Ovens.Code G n)
    (h : ∃ b : ℕ → ℝ, (∀ i, Switch.Paid
      (fun y : Ω × Config G n => fun t k => K y.1 t k i y.2) (b i)) ∧
      Ac.Hit (fun i => (P.activities.forced i).support) P.p.B b α W)
    (s : V → Support n)
    (hs : ∀ x i U q, (Photo.Fleece (K x) R z i U).part q ≠ 0 →
      ∀ v ∈ q.val, s v ⊆ (P.activities.forced i).support) :
    ∃ a : ℕ × R.Mode → ℝ, (∀ i, 0 ≤ a i) ∧
      (∀ i q, (∃ v ∈ q.val, ¬ s v ⊆ (P.activities.forced i).support) → a (i,q) = 0) ∧
      (∀ x i U q, ‖(Photo.Fleece (K x) R z i U).part q‖ ≤ a (i,q)) ∧
      Ac.Hit (fun i => (P.activities.forced i).support) P.p.B
        (fun i => ∑ q : R.Mode, Poly.toll w q * a (i,q)) α W := by
  obtain ⟨b, hb, hhit⟩ := h
  exact forced_of_loci hw (fun i => (P.activities.forced i).support) P.p.B
    (fun x => Photo.Fleece (K x) R z) ⟨b, fun i => Accent.crystal (hb i) hw hz, hhit⟩ s hs

/-- A single actual switch supplies exactly the uniform credit on a constant
test family. This applies in particular to one fixed incoming Cadence. -/
theorem credit_of_pays [Fintype ι] {P : Rep G n} {α W : ℝ}
    {K : ℝ → Finset ι → Ovens.Code G n} (h : Motion.Pays P.activities P.p K W α) :
    ∃ b : ℕ → ℝ, (∀ i, Switch.Paid
      (fun y : Ω × Config G n => fun t k => K t k i y.2) (b i)) ∧
      Ac.Hit (fun i => (P.activities.forced i).support) P.p.B b α W := by
  obtain ⟨b, hb, hhit⟩ := h.bought
  refine ⟨b, ?_, hhit⟩
  intro i
  obtain ⟨c, hc, hcost, hmodel⟩ := hb i
  exact ⟨c, hc, hcost, fun y => hmodel y.2⟩

end YM.Integration.QLocalCoefficientPublication
end
