import YM.Integration.CoveredSignedSeries
import YM.Integration.LocalComparisonEnvelopeDensity
import YM.Integration.KBoundGas

/-! Exact signed cofactors of the original compulsory-cover gas.
All remaining inventories and complete supports are retained. The estimates
used here establish convergence only; no relative cofactor bound is assumed. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativeTasteCoveredCofactor
open Function Finset Lattice Wilson RG Marker Overlay
open RG3.Forms RG3.Script.Picnic LocalComparison
open SectorNext.Vacuum Push.AbsoluteSums
open scoped Classical BigOperators

/-- KBound supplies a summable majorant for every target admissibility budget. -/
private theorem gas_absolute {G : Gauge} {n : Side} {P : Rep G n}
    {pK : BudgetPoint} {vacuum : ℝ} (hK : P.activities.KBound pK vacuum)
    (p0 : BudgetPoint) (U : Config G n) :
    Summable (fun s : Finset ℕ => ‖P.activities.gasOccurrence p0 s U‖) := by
  obtain ⟨b, hb, h⟩ := Activities.K_total hK
  have hDom : Dominated (P.activities.gasOccurrence p0) := by
    refine ⟨fun t => ∏ i ∈ t, b i,
      summable_finsetProd_of_summable_nonneg (fun i => (h i).1) hb, ?_⟩
    intro s U
    unfold Activities.gasOccurrence
    split
    · rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => (h i).2 U)
    rw [norm_zero]
    exact Finset.prod_nonneg fun i _ => (h i).1
  exact hDom.absolute U

variable {V : Type} [DecidableEq V] {Γ : Census V}
    {G : Gauge} {n : Side} {P : Rep G n}

/-- The original unmarked row, on the unchanged Nat address. -/
def scalarRow (P : Rep G n) (U : Config G n) (i : ℕ) : Poly Γ :=
  Poly.bead Γ (P.activities.K i U : ℂ)

/-- Ordered signed cofactor; the remaining rows cover all flags except the
distinguished inventory, and avoid its entire original support. -/
def cofactor (D : Deck Γ P) (U : Config G n) (i : ℕ) (s : Finset ℕ) : Poly Γ :=
  CoveredSignedCofactors.cofactorTerm
    (fun j => (P.activities.forced j).support)
    (fun j => (P.activities.forced j).inventory)
    (flags P.p.threshold U) (fun j => D.contents.each j U) (scalarRow P U) i s

/-- The complete signed sum, with every original marked row and cofactor. -/
def series (D : Deck Γ P) (U : Config G n) : Poly Γ :=
  ∑' i, (D.contents.each i U - scalarRow P U i) * ∑' s, cofactor D U i s

theorem cofactor_support (D : Deck Γ P) (U : Config G n)
    (i : ℕ) (s : Finset ℕ) (h : cofactor D U i s ≠ 0) :
    i ∈ s ∧ CoveredSignedCofactors.Pinned
      (fun j => (P.activities.forced j).support)
      (fun j => (P.activities.forced j).inventory)
      (flags P.p.threshold U) i (s.erase i) := by
  by_contra hn
  exact h (by simp only [cofactor, CoveredSignedCofactors.cofactorTerm, if_neg hn])

private theorem bead_eq (z : ℂ) : Poly.bead Γ z = z • (1 : Poly Γ) := by
  simpa only [mul_one] using Poly.product_bead (1 : Poly Γ) z

variable [Fintype V]
variable {X : Type*} {o : V → Site n} {T : Taste X o P Γ}
    {p pK : BudgetPoint} {w : V → ℝ} {κ regularPrice forcedPrice vacuum : ℝ}

private theorem row_bounds
    (h : FullBudget p T w κ regularPrice forcedPrice)
    (hK : P.activities.KBound pK vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1)
    (x : X) (U : Config G n) :
    ∃ b : ℕ → ℝ,
      (∀ i, Poly.price w ((T.leaf x).contents.each i U) ≤ b i) ∧
      (∀ i, Poly.price w (scalarRow P U i : Poly Γ) ≤ b i) ∧
      (∀ z : Site n, ∀ I : Finset ℕ,
        (∑ i ∈ I, if z ∈ (P.activities.forced i).inventory then b i else 0) ≤ 1) ∧
      SumBudget (fun i => Poly.price w
        ((T.leaf x).contents.each i U - scalarRow P U i))
        ((Fintype.card V : ℝ) * (κ * forcedPrice)) := by
  let q (ij : ℕ × ℕ) := Poly.toll w (T.menu.marks ij.1 ij.2) *
    p.mass (P.activities.forced ij.1).support (h.black ij)
  have hq0 (ij) : 0 ≤ q ij :=
    mul_nonneg (Poly.worth h.radii _).le
      ((h.black_nonnegative ij).trans (p.loMass _ _ (h.black_nonnegative ij)))
  have hq : SumBudget q ((Fintype.card V : ℝ) * (κ * forcedPrice)) :=
    Overlay.per_system hq0
      (fun ij => (h.active x).articles.occurs ij.1 ij.2) h.forcedTotal
  obtain ⟨hFiber, hOuter⟩ :=
    (summable_prod_of_nonneg (show 0 ≤ q from hq0)).mp hq.2.1
  let a (i : ℕ) := ∑' j, q (i, j)
  have ha (i) : 0 ≤ a i := tsum_nonneg (fun j => hq0 (i, j))
  have hA : SumBudget a ((Fintype.card V : ℝ) * (κ * forcedPrice)) :=
    ⟨ha, hOuter, (hq.2.1.tsum_prod).symm.trans_le hq.2.2⟩
  have hTag (i j) : Poly.price w ((T.leaf x).contents.tagged i j U) ≤ q (i, j) := by
    change Poly.price w (Poly.send (T.menu.marks i j) (T.menu.force x i j U)) ≤ _
    rw [Poly.solo]
    exact mul_le_mul_of_nonneg_left
      ((h.forced x i j U).trans (p.loMass _ _ (h.black_nonnegative (i, j))))
      (Poly.worth h.radii _).le
  have hRow (i) : Poly.price w
      ((T.leaf x).contents.each i U - scalarRow P U i) ≤ a i := by
    change Poly.price w ((Poly.bead Γ (P.activities.K i U : ℂ) +
      ∑' j, (T.leaf x).contents.tagged i j U) -
        Poly.bead Γ (P.activities.K i U : ℂ)) ≤ _
    rw [add_sub_cancel_left]
    exact (Poly.budgeted h.radii (hFiber i) (hTag i)).2
  obtain ⟨k, hk, hHit⟩ := hK
  have hScalar (i) : Poly.price w (scalarRow P U i : Poly Γ) ≤ k i := by
    change Poly.price w (Poly.send Γ.quiet (P.activities.K i U : ℂ)) ≤ _
    rw [Poly.solo, Poly.quiet_toll, one_mul, Complex.norm_real]
    exact (hk i).2 U
  have hBase (z : Site n) (I : Finset ℕ) :
      (∑ i ∈ I, if z ∈ (P.activities.forced i).inventory then k i else 0) ≤ vacuum := by
    apply le_trans _ (budget_sum (hHit z) I)
    apply sum_le_sum
    intro i _
    by_cases hz : z ∈ (P.activities.forced i).inventory
    · have hs := (P.activities.forced i).inventory_sup hz
      simp only [if_pos hz, if_pos hs]
      exact pK.loMass _ _ (hk i).1
    · rw [if_neg hz]
      split
      · exact (hk i).1.trans (pK.loMass _ _ (hk i).1)
      · exact le_rfl
  refine ⟨fun i => k i + a i, ?_, ?_, ?_, ?_⟩
  · intro i
    have hh := Poly.addition h.radii
      ((T.leaf x).contents.each i U - scalarRow P U i) (scalarRow P U i)
    rw [sub_add_cancel] at hh
    exact (hh.trans (add_le_add (hRow i) (hScalar i))).trans_eq (add_comm _ _)
  · intro i
    exact (hScalar i).trans (le_add_of_nonneg_right (ha i))
  · intro z I
    calc
      _ ≤ (∑ i ∈ I, if z ∈ (P.activities.forced i).inventory then k i else 0) +
          ∑ i ∈ I, a i := by
        rw [← sum_add_distrib]
        apply sum_le_sum
        intro i _
        by_cases hz : z ∈ (P.activities.forced i).inventory
        · simpa only [if_pos hz] using le_refl (k i + a i)
        · simpa only [if_neg hz, zero_add] using ha i
      _ ≤ vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) :=
        add_le_add (hBase z I) (budget_sum hA I)
      _ ≤ 1 := hSmall
  · exact budget_mono hA (fun _ => Poly.nonnegative h.radii _) hRow

private theorem bands_series (D : Deck Γ P) (U : Config G n) (w : V → ℝ)
    (hw : ∀ v, 0 < w v) (b : ℕ → ℝ)
    (hF : ∀ i, Poly.price w (D.contents.each i U) ≤ b i)
    (hG : ∀ i, Poly.price w (scalarRow P U i : Poly Γ) ≤ b i)
    (hHit : ∀ z : Site n, ∀ I : Finset ℕ,
      (∑ i ∈ I, if z ∈ (P.activities.forced i).inventory then b i else 0) ≤ 1)
    {e : ℝ}
    (hTail : SumBudget (fun i => Poly.price w
      (D.contents.each i U - scalarRow P U i)) e)
    (hGas : Summable (fun s : Finset ℕ => ‖P.activities.gasOccurrence P.p s U‖)) :
    (∀ i, Summable (cofactor D U i)) ∧
      Summable (fun i => (D.contents.each i U - scalarRow P U i) *
        ∑' s, cofactor D U i s) ∧
      forcedClusterError D U = series D U := by
  let K (i : ℕ) := (P.activities.forced i).support
  let Z (i : ℕ) := (P.activities.forced i).inventory
  let F (i : ℕ) := D.contents.each i U
  let G (i : ℕ) := (scalarRow P U i : Poly Γ)
  let A := flags P.p.threshold U
  have hZ (i) : Z i ⊆ K i := (P.activities.forced i).inventory_sup
  have hN (i) : (Z i).Nonempty := (P.activities.forced i).inventory_ne
  have hSeries := CoveredSignedSeries.series hw K Z hZ hN (le_refl (1 : ℝ))
    F G b hF hG hHit hTail A
  let term (s : Finset ℕ) (i : ℕ) := (F i - G i) *
    CoveredSignedCofactors.cofactorTerm K Z A F G i s
  have hJoint : Summable (Function.uncurry term) := by
    have h := CoveredSignedSeries.joint_budget hw K Z hZ hN (le_refl (1 : ℝ))
      F G b hF hG hHit hTail A
    exact (Poly.budgeted hw h.2.1 (fun _ => le_rfl)).1
  have hFinite (s : Finset ℕ) : (∑' i, term s i) = ∑ i ∈ s, term s i := by
    apply tsum_eq_sum
    intro i hi
    simp only [term, CoveredSignedCofactors.cofactorTerm, hi, false_and,
      if_false, mul_zero]
  have hPacket (s : Finset ℕ) :
      (if accounted K Z A s then (∏ i ∈ s, F i) - ∏ i ∈ s, G i else 0) =
        D.contents.packet s U - Poly.bead Γ (P.activities.gasOccurrence P.p s U : ℂ) := by
    have hAd : accounted K Z A s ↔ P.activities.admissible P.p U s := by
      apply iff_of_eq
      unfold accounted Activities.admissible K Z A
      congr!
    rw [hAd]
    dsimp only [F, G]
    by_cases hs : P.activities.admissible P.p U s
    · simp only [if_pos hs, Bands.packet, Activities.gasOccurrence,
        scalarRow, Complex.ofReal_prod, map_prod]
    · simp only [if_neg hs, Bands.packet, Activities.gasOccurrence,
        Complex.ofReal_zero, map_zero, sub_self]
  have hDelta : Summable (fun s : Finset ℕ =>
      D.contents.packet s U - Poly.bead Γ (P.activities.gasOccurrence P.p s U : ℂ)) :=
    hJoint.prod.congr (fun s => (hFinite s).trans
      ((CoveredSignedCofactors.packet_difference K Z hZ A F G s).symm.trans (hPacket s)))
  have hVac : Summable (fun s : Finset ℕ =>
      Poly.bead Γ (P.activities.gasOccurrence P.p s U : ℂ)) := by
    apply (Poly.budgeted hw hGas ?_).1
    intro s
    change Poly.price w (Poly.send Γ.quiet
      (P.activities.gasOccurrence P.p s U : ℂ)) ≤ _
    rw [Poly.solo, Poly.quiet_toll, one_mul, Complex.norm_real]
  have hFull : Summable (fun s : Finset ℕ => D.contents.packet s U) := by
    simpa only [sub_add_cancel] using hDelta.add hVac
  have hVacSum : (∑' s : Finset ℕ,
      Poly.bead Γ (P.activities.gasOccurrence P.p s U : ℂ)) =
        Poly.bead Γ (P.activities.gas P.p U : ℂ) := by
    ext q
    rw [Poly.share hVac]
    change (∑' s : Finset ℕ,
      (Poly.send Γ.quiet (P.activities.gasOccurrence P.p s U : ℂ)).part q) =
        (Poly.send Γ.quiet (P.activities.gas P.p U : ℂ)).part q
    simp only [Poly.part_send]
    by_cases hq : q = Γ.quiet
    · subst q
      simp only [ite_true, Activities.gas, Complex.ofReal_tsum]
    · simp only [if_neg hq, tsum_zero]
  refine ⟨hSeries.1, hSeries.2.1, ?_⟩
  unfold forcedClusterError series Bands.cluster
  rw [← bead_eq, ← hVacSum, ← hFull.tsum_sub hVac]
  exact (tsum_congr (fun s => (hPacket s).symm)).trans hSeries.2.2

/-- Exact physical signed cofactors under the existing full relative budget.
The common prices establish absolute convergence, not a normalized cofactor
estimate. Neither the compulsory flags nor the original K rows are changed. -/
theorem relative_series
    {cost : V → ℝ}
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (hK : P.activities.KBound pK vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1)
    (x : X) (U : Config G n) :
    (∀ i, Summable (cofactor (T.leaf x) U i)) ∧
      Summable (fun i => ((T.leaf x).contents.each i U - scalarRow P U i) *
        ∑' s, cofactor (T.leaf x) U i s) ∧
      forcedClusterError (T.leaf x) U = series (T.leaf x) U := by
  obtain ⟨b, hF, hG, hHit, hTail⟩ := row_bounds h.budget hK hSmall x U
  let w' := fun v => w v / cost v
  have hw' (v) : 0 < w' v := div_pos (h.budget.radii v) (hc v)
  let E : Poly Γ ≃L[ℂ] Poly Γ :=
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc)
  have hE (i) : E (scalarRow P U i : Poly Γ) = scalarRow P U i := by
    change E (Poly.bead Γ _) = Poly.bead Γ _
    rw [bead_eq, map_smul]
    exact congrArg (fun z : Poly Γ => (P.activities.K i U : ℂ) • z)
      (restoreEnvelope_product_one cost hc)
  have hEach (i) : Poly.price w' ((T.leaf x).contents.each i U) =
      Poly.price w (((priceNormalized (envelopeProduct cost) T).leaf x).contents.each i U) := by
    rw [← restoreEnvelope_each T cost hc x i U, restoreEnvelope_product_price cost w hc]
  have hScalar (i) : Poly.price w' (scalarRow P U i : Poly Γ) =
      Poly.price w (scalarRow P U i : Poly Γ) := by
    change Poly.price w' (Poly.send Γ.quiet (P.activities.K i U : ℂ)) =
      Poly.price w (Poly.send Γ.quiet (P.activities.K i U : ℂ))
    simp only [Poly.solo, Poly.quiet_toll]
  have hDifference (i) : Poly.price w'
      ((T.leaf x).contents.each i U - scalarRow P U i) =
      Poly.price w ((((priceNormalized (envelopeProduct cost) T).leaf x).contents.each i U) -
        scalarRow P U i) := by
    have he : E
        ((((priceNormalized (envelopeProduct cost) T).leaf x).contents.each i U) -
          scalarRow P U i) = (T.leaf x).contents.each i U - scalarRow P U i := by
      rw [map_sub, hE]
      exact congrArg (fun z : Poly Γ => z - scalarRow P U i)
        (restoreEnvelope_each T cost hc x i U)
    rw [← he]
    exact restoreEnvelope_product_price cost w hc _
  apply bands_series (T.leaf x) U w' hw' b
    (fun i => (hEach i).trans_le (hF i))
    (fun i => (hScalar i).trans_le (hG i)) hHit
  · exact budget_mono hTail (fun _ => Poly.nonnegative hw' _)
      (fun i => (hDifference i).le)
  · exact gas_absolute hK P.p U

end YM.Integration.NativeTasteCoveredCofactor
end
