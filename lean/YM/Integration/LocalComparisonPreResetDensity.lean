import YM.Integration.LocalComparisonFullDensity

/-!
# Full density control before affine normalization

This is the same finite-cover proof as LocalComparisonForcedCover, with
its actual hypothesis made explicit: the original vacuum gas has an
absolutely summable series. A native KBound supplies that series without
requiring value-nullness or affine-nullness of the regular vacuum rows.
No carrier, forced address, eligible predicate, or physical density changes.
The source proof is retained in `YM.Integration.LocalComparisonForcedCover`.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison.PreResetDensity

open Function Finset RG Lattice Wilson Marker Overlay RG3.Forms RG3.Script.Picnic
open SectorNext.Vacuum Trace13.Response Push.AbsoluteSums
open ForcedCover
open scoped BigOperators Classical

variable {V : Type} [DecidableEq V] {R : Census V}
    {G : Gauge} {n : Side} {P : Rep G n}

/-- Absolute gas summability uses only the original K bound. The mask
point and the point used to pay support can be different. -/
theorem gasSeries {A : Activities G n} {p pK : BudgetPoint} {vacuum : ℝ}
    (h : A.KBound pK vacuum) : Dominated (A.gasOccurrence p) := by
  obtain ⟨b, hb, hbnd⟩ := Activities.K_total h
  refine ⟨fun t => ∏ i ∈ t, b i,
    summable_finsetProd_of_summable_nonneg (fun i => (hbnd i).1) hb, ?_⟩
  intro i U
  unfold Activities.gasOccurrence
  split
  · rw [norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun k _ => (hbnd k).2 U)
  rw [norm_zero]
  exact Finset.prod_nonneg fun k _ => (hbnd k).1

theorem cluster_difference (B : Bands R P) (w : V → ℝ) (hw : ∀ x, 0 < w x)
    (U : Config G n)
    (hGas : Summable (fun s : Finset ℕ => ‖P.activities.gasOccurrence P.p s U‖)) (k a : ℕ → ℝ)
    (hk : ∀ i, 0 ≤ k i) (ha : ∀ i, 0 ≤ a i)
    (hK : ∀ i, ‖P.activities.K i U‖ ≤ k i)
    (hMark : ∀ i, Poly.price w
      (B.each i U - Poly.bead R (P.activities.K i U : ℂ)) ≤ a i)
    (γ M : ℝ)
    (hHit : ∀ x : Site n, ∀ I : Finset ℕ,
      (∑ i ∈ I, if x ∈ (P.activities.forced i).inventory then
        (k i + a i) * Real.exp (γ * (P.activities.forced i).inventory.card) else 0) ≤ 1)
    (hMarked : ∀ I : Finset ℕ,
      (∑ i ∈ I, a i * Real.exp (γ * (P.activities.forced i).inventory.card)) ≤ M) :
    Poly.price w (B.cluster U - Poly.bead R (P.activities.gas P.p U : ℂ)) ≤
      M * Real.exp (-γ * (flags P.p.threshold U).card) := by
  let X (i : ℕ) := (P.activities.forced i).support
  let Z (i : ℕ) := (P.activities.forced i).inventory
  let D := flags P.p.threshold U
  let v (i : ℕ) := k i + a i
  let E (s : Finset ℕ) :=
    B.packet s U - Poly.bead R (P.activities.gasOccurrence P.p s U : ℂ)
  have hv (i) : 0 ≤ v i := add_nonneg (hk i) (ha i)
  have hScalar (i) : Poly.price w (Poly.bead R (P.activities.K i U : ℂ)) ≤ k i := by
    change Poly.price w (Poly.send R.quiet (P.activities.K i U : ℂ)) ≤ k i
    rw [Poly.solo, Poly.quiet_toll, one_mul, Complex.norm_real]
    exact hK i
  have hEach (i) : Poly.price w (B.each i U) ≤ v i := by
    have h := Poly.addition hw
      (B.each i U - Poly.bead R (P.activities.K i U : ℂ))
      (Poly.bead R (P.activities.K i U : ℂ))
    rw [sub_add_cancel] at h
    exact (h.trans (add_le_add (hMark i) (hScalar i))).trans_eq (add_comm _ _)
  have hPacket (s : Finset ℕ) (hs : P.activities.admissible P.p U s) :
      Poly.price w (E s) ≤ fee v a s := by
    unfold E Bands.packet Activities.gasOccurrence
    rw [if_pos hs, if_pos hs, Complex.ofReal_prod, map_prod]
    exact product_difference w hw (fun i => B.each i U)
      (fun i => Poly.bead R (P.activities.K i U : ℂ)) v a hv ha hEach
      (fun i => (hScalar i).trans (le_add_of_nonneg_right (ha i))) hMark s
  have hZero (s : Finset ℕ) (hs : ¬P.activities.admissible P.p U s) : E s = 0 := by
    simp only [E, Bands.packet, Activities.gasOccurrence, if_neg hs,
      Complex.ofReal_zero, map_zero, sub_self]
  have hCost : SumBudget (fun s => Poly.price w (E s))
      (M * Real.exp (-γ * D.card)) := by
    apply budget_of_sum (fun s => Poly.nonnegative hw _)
    intro S
    let I := S.biUnion id
    let F := S.filter (P.activities.admissible P.p U)
    have hSubset : F ⊆ I.powerset.filter (accounted X Z D) := by
      intro s hs
      obtain ⟨hsS, hs⟩ := mem_filter.mp hs
      have he : P.activities.admissible P.p U s = accounted X Z D s := by
        unfold Activities.admissible accounted X Z D
        congr!
      exact mem_filter.mpr ⟨mem_powerset.mpr
        (fun i hi => mem_biUnion.mpr ⟨s, hsS, hi⟩), he ▸ hs⟩
    calc
      _ = ∑ s ∈ F, Poly.price w (E s) := by
        symm
        apply sum_subset (filter_subset ..)
        intro s hs hNot
        have h : ¬P.activities.admissible P.p U s :=
          fun h => hNot (mem_filter.mpr ⟨hs, h⟩)
        rw [hZero s h, Poly.zero_price]
      _ ≤ ∑ s ∈ F, fee v a s :=
        sum_le_sum (fun s hs => hPacket s (mem_filter.mp hs).2)
      _ ≤ ∑ s ∈ I.powerset.filter (accounted X Z D), fee v a s :=
        sum_le_sum_of_subset_of_nonneg hSubset
          (fun s _ _ => by
            unfold fee
            exact sum_nonneg
              (fun i _ => mul_nonneg (ha i) (prod_nonneg (fun j _ => hv j))))
      _ ≤ _ := marked_cover X Z (fun i => (P.activities.forced i).inventory_sup)
        (fun i => (P.activities.forced i).inventory_ne) v a hv ha γ M
        (fun x I => by convert hHit x I using 1; congr!) hMarked D I
  obtain ⟨hE, hEPrice⟩ := Poly.budgeted hw hCost.2.1 (fun _ => le_rfl)
  have hGas : Summable (fun s : Finset ℕ =>
      Poly.bead R (P.activities.gasOccurrence P.p s U : ℂ)) := by
    apply (Poly.budgeted hw hGas ?_).1
    intro s
    change Poly.price w (Poly.send R.quiet
      (P.activities.gasOccurrence P.p s U : ℂ)) ≤ _
    rw [Poly.solo, Poly.quiet_toll, one_mul, Complex.norm_real]
  have hB : Summable (fun s => B.packet s U) := by
    simpa only [E, sub_add_cancel] using hE.add hGas
  have hGasSum : (∑' s : Finset ℕ,
      Poly.bead R (P.activities.gasOccurrence P.p s U : ℂ)) =
      Poly.bead R (P.activities.gas P.p U : ℂ) := by
    change (∑' s : Finset ℕ, Poly.send R.quiet
      (P.activities.gasOccurrence P.p s U : ℂ)) =
      Poly.send R.quiet (P.activities.gas P.p U : ℂ)
    have hSend : Summable (fun s : Finset ℕ => Poly.send R.quiet
        (P.activities.gasOccurrence P.p s U : ℂ)) := hGas
    ext j
    rw [Poly.share hSend]
    by_cases hj : j = R.quiet
    · subst j
      simp only [Poly.part_send, ite_true, Activities.gas, Complex.ofReal_tsum]
    simp only [Poly.part_send, if_neg hj, tsum_zero]
  have hSum : (∑' s, E s) = B.cluster U -
      Poly.bead R (P.activities.gas P.p U : ℂ) := by
    rw [show (∑' s, E s) = (∑' s, B.packet s U) -
      ∑' s, Poly.bead R (P.activities.gasOccurrence P.p s U : ℂ) from hB.tsum_sub hGas]
    rw [hGasSum]
    rfl
  rw [← hSum]
  exact hEPrice.trans hCost.2.2


variable [Fintype V]
    {p : BudgetPoint} {X : Type*} {o : V → Site n}
    {T : Taste X o P R} {w : V → ℝ} {κ regularPrice forcedPrice : ℝ}

omit [Fintype V] in
private theorem bead_eq_smul_one (z : ℂ) :
    Poly.bead R z = z • (1 : Poly R) := by
  simpa only [mul_one] using Poly.product_bead (1 : Poly R) z

theorem full_forced_cluster_price
    (h : FullBudget p T w κ regularPrice forcedPrice)
    {pK : BudgetPoint} {vacuum : ℝ}
    (hReserve : P.activities.KBound pK vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1)
    (x : X) (U : Config G n) :
    Poly.price w (forcedClusterError (T.leaf x) U) ≤
      ((Fintype.card V : ℝ) * (κ * forcedPrice)) *
        Real.exp (-min (flagRate pK) (flagRate p) * (flags P.p.threshold U).card) := by
  have hGas := (gasSeries (p := P.p) hReserve).absolute U
  let M := (Fintype.card V : ℝ) * (κ * forcedPrice)
  let γ := min (flagRate pK) (flagRate p)
  let B := (T.leaf x).contents
  let Z (i : ℕ) := (P.activities.forced i).inventory
  let q (ij : ℕ × ℕ) := Poly.toll w (T.menu.marks ij.1 ij.2) *
    p.mass (P.activities.forced ij.1).support (h.black ij)
  have hqNonnegative (ij) : 0 ≤ q ij :=
    mul_nonneg (Poly.worth h.radii _).le
      ((h.black_nonnegative ij).trans (p.loMass _ _ (h.black_nonnegative ij)))
  have hq : SumBudget q M :=
    Overlay.per_system hqNonnegative
      (fun ij => (h.active x).articles.occurs ij.1 ij.2) h.forcedTotal
  obtain ⟨hFiber, hOuter⟩ :=
    (summable_prod_of_nonneg (show 0 ≤ q from hqNonnegative)).mp hq.2.1
  let b (i : ℕ) := ∑' j, q (i, j)
  let a (i : ℕ) := Real.exp (-γ * (Z i).card) * b i
  have hb (i) : 0 ≤ b i := tsum_nonneg (fun j => hqNonnegative (i, j))
  have ha (i) : 0 ≤ a i := mul_nonneg (Real.exp_pos _).le (hb i)
  have hRestore (i) : a i * Real.exp (γ * (Z i).card) = b i := by
    change (Real.exp (-γ * (Z i).card) * b i) * Real.exp (γ * (Z i).card) = b i
    calc
      _ = (Real.exp (-γ * (Z i).card) * Real.exp (γ * (Z i).card)) * b i := by ring
      _ = _ := by
        rw [← Real.exp_add, show -γ * (Z i).card + γ * (Z i).card = 0 by ring,
          Real.exp_zero, one_mul]
  have hMarked (I : Finset ℕ) :
      (∑ i ∈ I, a i * Real.exp (γ * (Z i).card)) ≤ M := by
    simp_rw [hRestore]
    exact (hOuter.sum_le_tsum I (fun i _ => hb i)).trans
      ((hq.2.1.tsum_prod).symm.trans_le hq.2.2)
  have hInventoryBase (i) : γ * (Z i).card ≤
      pK.supportExponent * coverNumber pK.B (P.activities.forced i).support :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)).trans
      (inventory_pay pK (P.activities.forced i).inventory_sup)
  have hInventoryMarked (i) : γ * (Z i).card ≤
      p.supportExponent * coverNumber p.B (P.activities.forced i).support :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)).trans
      (inventory_pay p (P.activities.forced i).inventory_sup)
  have hCompensate (i) : 1 ≤ Real.exp (-γ * (Z i).card) *
      Real.exp (p.supportExponent * coverNumber p.B (P.activities.forced i).support) := by
    rw [← Real.exp_add]
    apply Real.one_le_exp
    linarith only [hInventoryMarked i]
  have hTagged (i j : ℕ) : Poly.price w (B.tagged i j U) ≤
      Real.exp (-γ * (Z i).card) * q (i, j) := by
    change Poly.price w (Poly.send (T.menu.marks i j) (T.menu.force x i j U)) ≤ _
    rw [Poly.solo]
    calc
      _ ≤ Poly.toll w (T.menu.marks i j) * h.black (i, j) :=
        mul_le_mul_of_nonneg_left (h.forced x i j U) (Poly.worth h.radii _).le
      _ = 1 * (Poly.toll w (T.menu.marks i j) * h.black (i, j)) := by ring
      _ ≤ (Real.exp (-γ * (Z i).card) * Real.exp
          (p.supportExponent * coverNumber p.B (P.activities.forced i).support)) *
          (Poly.toll w (T.menu.marks i j) * h.black (i, j)) :=
        mul_le_mul_of_nonneg_right (hCompensate i)
          (mul_nonneg (Poly.worth h.radii _).le (h.black_nonnegative _))
      _ = _ := by unfold q BudgetPoint.mass; ring
  have hMark (i) : Poly.price w
      (B.each i U - Poly.bead R (P.activities.K i U : ℂ)) ≤ a i := by
    change Poly.price w ((Poly.bead R (P.activities.K i U : ℂ) +
      ∑' j, B.tagged i j U) - Poly.bead R (P.activities.K i U : ℂ)) ≤ a i
    rw [add_sub_cancel_left]
    obtain ⟨_, hPrice⟩ := Poly.budgeted h.radii
      ((hFiber i).mul_left (Real.exp (-γ * (Z i).card))) (hTagged i)
    exact hPrice.trans_eq (by rw [tsum_mul_left])
  obtain ⟨k, hk, hK⟩ := hReserve
  have hBaseHit (y : Site n) (I : Finset ℕ) :
      (∑ i ∈ I, if y ∈ Z i then k i * Real.exp (γ * (Z i).card) else 0) ≤ vacuum := by
    apply le_trans _ (budget_sum (hK y) I)
    apply sum_le_sum
    intro i _
    split_ifs with hZ hSupport
    · unfold BudgetPoint.mass
      rw [mul_comm (k i)]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hInventoryBase i)) (hk i).1
    · exact False.elim (hSupport ((P.activities.forced i).inventory_sup hZ))
    · exact (hk i).1.trans (pK.loMass _ _ (hk i).1)
    exact le_rfl
  have hHit (y : Site n) (I : Finset ℕ) :
      (∑ i ∈ I, if y ∈ Z i then
        (k i + a i) * Real.exp (γ * (Z i).card) else 0) ≤ 1 := by
    calc
      _ ≤ (∑ i ∈ I, if y ∈ Z i then k i * Real.exp (γ * (Z i).card) else 0) +
          ∑ i ∈ I, a i * Real.exp (γ * (Z i).card) := by
        rw [← sum_add_distrib]
        apply sum_le_sum
        intro i _
        split_ifs
        · exact (add_mul ..).le
        exact le_add_of_nonneg_right (mul_nonneg (ha i) (Real.exp_pos _).le)
      _ ≤ vacuum + M := add_le_add (hBaseHit y I) (hMarked I)
      _ ≤ 1 := hSmall
  change Poly.price w (B.cluster U - (P.activities.gas P.p U : ℂ) • (1 : Poly R)) ≤ _
  rw [← bead_eq_smul_one]
  exact cluster_difference B w h.radii U hGas k a
    (fun i => (hk i).1) ha (fun i => (hk i).2 U) hMark γ M hHit hMarked

/-- Full independent-test forced bound, with exact support on flagged
fields, for the unchanged physical coefficients and kernel envelopes. -/
theorem relative_forced_cluster_price_flagged {cost : V → ℝ}
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v) {vacuum : ℝ}
    (hReserve : P.activities.KBound p vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1)
    (x : X) (U : Config G n) :
    Poly.price (fun v => w v / cost v) (forcedClusterError (T.leaf x) U) ≤
      if flags P.p.threshold U = ∅ then 0 else
        ((Fintype.card V : ℝ) * (κ * forcedPrice)) *
          Real.exp (-flagRate p * (flags P.p.threshold U).card) := by
  split_ifs with hFlags
  · rw [forcedClusterError_zero (T.leaf x) U hFlags, Poly.zero_price]
  rw [forcedClusterError_product_price T cost hcost w x U]
  simpa only [min_self] using full_forced_cluster_price h.budget hReserve hSmall x U

/-- Every regular, forced, and mixed coefficient is retained, without
an affine-null restriction on the unmarked vacuum. -/
theorem full_density_error_price {cost : V → ℝ}
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v) (hthreshold : p.threshold = P.p.threshold)
    {vacuum : ℝ} (hReserve : P.activities.KBound p vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1)
    (x : X) (U : Config G n) :
    Poly.price (fun v => w v / cost v)
      ((T.leaf x).density U - (P.eval U : ℂ) • (1 : Poly R)) ≤
      |P.eval U| * (Real.exp (Fintype.card V * regularPrice) - 1) +
      (Real.exp (P.exponent U) * Real.exp (Fintype.card V * regularPrice)) *
        (if flags P.p.threshold U = ∅ then 0 else
          ((Fintype.card V : ℝ) * (κ * forcedPrice)) *
            Real.exp (-flagRate p * (flags P.p.threshold U).card)) := by
  apply (h.density_error_price hcost hthreshold x U).trans
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left
    (relative_forced_cluster_price_flagged h hcost hReserve hSmall x U)
    (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)

end YM.Integration.LocalComparison.PreResetDensity
