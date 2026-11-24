import YM.Integration.LocalComparisonEnvelopeDensity
import YM.SectorNext.VACUUM_NORMALIZATION.Covered
import YM.Trace13.GasCredit

/-!
Compulsory-cover bounds for the complete marked forced numerator.

The combinatorics retain the actual disjoint support condition and exact
coverage of the flag inventory. There is no sum over arbitrary choices of
the flag set here, and no division by the vacuum gas. Integrating the final
bound against the exponential part of the physical density, uniformly in
volume, remains a separate analytic obligation.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison.ForcedCover

open Function Finset RG Lattice Wilson Marker
open SectorNext.Vacuum Trace13.Response Push.AbsoluteSums
open scoped BigOperators Classical

variable {J : Type*}

/-- Charge one distinguished marked occurrence, while every other occurrence
uses the full combined hit budget. Exact coverage removes volume entropy. -/
theorem marked_cover (X Z : ℕ → Finset J)
    (hZ : ∀ i, Z i ⊆ X i) (hNonempty : ∀ i, (Z i).Nonempty)
    (v a : ℕ → ℝ) (hv : ∀ i, 0 ≤ v i) (ha : ∀ i, 0 ≤ a i)
    (γ M : ℝ)
    (hHit : ∀ x : J, ∀ I : Finset ℕ,
      (∑ i ∈ I, if x ∈ Z i then v i * Real.exp (γ * (Z i).card) else 0) ≤ 1)
    (hMarked : ∀ I : Finset ℕ,
      (∑ i ∈ I, a i * Real.exp (γ * (Z i).card)) ≤ M)
    (D : Finset J) (I : Finset ℕ) :
    (∑ s ∈ I.powerset.filter (accounted X Z D), fee v a s) ≤
      M * Real.exp (-γ * D.card) := by
  let F := I.powerset.filter (accounted X Z D)
  let R (i : ℕ) := F.filter (fun s => i ∈ s)
  have hF (s : Finset ℕ) (hs : s ∈ F) : s ⊆ I ∧ accounted X Z D s := by
    simpa only [F, mem_filter, mem_powerset] using hs
  have each (i : ℕ) :
      (∑ s ∈ R i, a i * ∏ j ∈ s.erase i, v j) ≤
        (a i * Real.exp (γ * (Z i).card)) * Real.exp (-γ * D.card) := by
    by_cases hR : (R i).Nonempty
    · obtain ⟨s, hs⟩ := hR
      have hsF : s ∈ F := (mem_filter.mp hs).1
      have hi : i ∈ s := (mem_filter.mp hs).2
      have hZD : Z i ⊆ D := minus X Z (hF s hsF).2 hZ i hi
      have hImage : (R i).image (fun s => s.erase i) ⊆
          I.powerset.filter (accounted X Z (D \ Z i)) := by
        intro t ht
        obtain ⟨u, hu, rfl⟩ := mem_image.mp ht
        obtain ⟨huF, hiu⟩ := mem_filter.mp hu
        refine mem_filter.mpr ⟨mem_powerset.mpr
          (fun j hj => (hF u huF).1 (mem_of_mem_erase hj)), ?_⟩
        convert reaccounts X Z (hF u huF).2 hZ i hiu using 1
        congr!
      have hExp : Real.exp (-γ * (D \ Z i).card) =
          Real.exp (γ * (Z i).card) * Real.exp (-γ * D.card) := by
        have hc : ((D \ Z i).card : ℝ) + (Z i).card = D.card := by
          exact_mod_cast card_sdiff_add_card_eq_card hZD
        rw [← Real.exp_add]
        congr 1
        rw [← hc]
        ring
      calc
        _ = a i * ∑ t ∈ (R i).image (fun s => s.erase i), ∏ j ∈ t, v j := by
          rw [sum_image]
          · rw [mul_sum]
          intro u hu t ht he
          change u.erase i = t.erase i at he
          rw [← insert_erase (mem_filter.mp hu).2,
            ← insert_erase (mem_filter.mp ht).2, he]
        _ ≤ a i * ∑ t ∈ I.powerset.filter (accounted X Z (D \ Z i)),
            ∏ j ∈ t, v j := by
          apply mul_le_mul_of_nonneg_left _ (ha i)
          exact sum_le_sum_of_subset_of_nonneg hImage
            (fun t _ _ => prod_nonneg (fun j _ => hv j))
        _ ≤ a i * Real.exp (-γ * (D \ Z i).card) := by
          apply mul_le_mul_of_nonneg_left _ (ha i)
          simpa only [ite_self, one_mul] using
            cover_power X Z hZ hNonempty (le_refl (1 : ℝ)) v hv hHit (D \ Z i) I
        _ = _ := by rw [hExp]; ring
    rw [not_nonempty_iff_eq_empty.mp hR, sum_empty]
    exact mul_nonneg (mul_nonneg (ha i) (Real.exp_pos _).le) (Real.exp_pos _).le
  calc
    _ = ∑ i ∈ I, ∑ s ∈ R i, a i * ∏ j ∈ s.erase i, v j := by
      change (∑ s ∈ F, fee v a s) = _
      simp_rw [R, sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro s hs
      have hFilter : I.filter (fun i => i ∈ s) = s := by
        ext i
        simp only [mem_filter]
        exact ⟨And.right, fun hi => ⟨(hF s hs).1 hi, hi⟩⟩
      rw [← sum_filter, hFilter]
      unfold fee
      congr!
    _ ≤ ∑ i ∈ I, (a i * Real.exp (γ * (Z i).card)) *
        Real.exp (-γ * D.card) := sum_le_sum (fun i _ => each i)
    _ = (∑ i ∈ I, a i * Real.exp (γ * (Z i).card)) *
        Real.exp (-γ * D.card) := (sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hMarked I) (Real.exp_pos _).le

variable {V : Type} [DecidableEq V] {R : Census V}

/-- Product subtraction with every mixed marked term retained. This bound
uses a distinguished differing factor, not a coefficientwise linearization. -/
theorem product_difference (w : V → ℝ) (hw : ∀ x, 0 < w x)
    (f g : ℕ → Poly R) (v a : ℕ → ℝ)
    (hv : ∀ i, 0 ≤ v i) (ha : ∀ i, 0 ≤ a i)
    (hf : ∀ i, Poly.price w (f i) ≤ v i)
    (hg : ∀ i, Poly.price w (g i) ≤ v i)
    (hDifference : ∀ i, Poly.price w (f i - g i) ≤ a i)
    (s : Finset ℕ) :
    Poly.price w ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) ≤ fee v a s := by
  have hProduct (s : Finset ℕ) : Poly.price w (∏ i ∈ s, f i) ≤ ∏ i ∈ s, v i :=
    (Poly.multiple hw s f).trans
      (prod_le_prod (fun i _ => Poly.nonnegative hw _) (fun i _ => hf i))
  induction s using Finset.induction_on with
  | empty => simp only [prod_empty, sub_self, Poly.zero_price, fee, sum_empty, le_refl]
  | @insert i s hi ih =>
    have hFee : fee v a (insert i s) =
        a i * (∏ j ∈ s, v j) + v i * fee v a s := by
      convert fee_add v a hi using 1
      congr!
    rw [prod_insert hi, prod_insert hi, hFee]
    rw [show f i * (∏ j ∈ s, f j) - g i * (∏ j ∈ s, g j) =
      (f i - g i) * (∏ j ∈ s, f j) +
        g i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j) by ring]
    apply (Poly.addition hw _ _).trans
    apply add_le_add
    · exact (Poly.multiplication hw _ _).trans
        (mul_le_mul (hDifference i) (hProduct s) (Poly.nonnegative hw _) (ha i))
    exact (Poly.multiplication hw _ _).trans
      (mul_le_mul (hg i) ih (Poly.nonnegative hw _) (hv i))

end YM.Integration.LocalComparison.ForcedCover

namespace YM.Integration.LocalComparison.ForcedCover

open Function Finset RG Lattice Wilson Marker Overlay
open SectorNext.Vacuum Trace13.Response Push.AbsoluteSums
open scoped BigOperators Classical

variable {V : Type} [DecidableEq V] {R : Census V}
    {G : Gauge} {n : Side} {P : Rep G n}

/-- Full marked cluster subtraction at one fixed field, assuming concrete
majorants for the individual original forced addresses. The distinguished
marked cost is summed only once; all its mixed companions are retained. -/
theorem cluster_difference (B : Bands R P) (w : V → ℝ) (hw : ∀ x, 0 < w x)
    {regular vacuum : ℝ} (hP : P.activities.Valid P.p regular vacuum)
    (U : Config G n) (k a : ℕ → ℝ)
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
    apply (Poly.budgeted hw ((Activities.gasSeries hP).absolute U) ?_).1
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

end YM.Integration.LocalComparison.ForcedCover

namespace YM.Integration.LocalComparison

open Function Finset RG Lattice Wilson Marker Overlay RG3.Forms RG3.Script.Picnic
open SectorNext.Vacuum Push.AbsoluteSums
open scoped BigOperators Classical

variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
    {G : Gauge} {n : Side} {P : Rep G n} {p : BudgetPoint} {X : Type*} {o : V → Site n}
    {T : Taste X o P R} {w : V → ℝ} {κ regularPrice forcedPrice : ℝ}

omit [Fintype V] in
/-- The physical scalar embedding used by the forced gas. -/
private theorem bead_eq_smul_one (z : ℂ) :
    Poly.bead R z = z • (1 : Poly R) := by
  simpa only [mul_one] using Poly.product_bead (1 : Poly R) z

/-- A full, test-uniform forced numerator bound from the announced rooted
representation norm. The only smallness condition is the explicit scalar
sum of the native vacuum hit cap and the total marked hit cap.

There is no factor counting ambient lattice sites. This theorem does not
bound the integral of the exponential density divided by its partition. -/
theorem FullBudget.forced_cluster_price_of_reserve
    (h : FullBudget p T w κ regularPrice forcedPrice)
    {pK : BudgetPoint} {regular actualVacuum vacuum : ℝ}
    (hP : P.activities.Valid P.p regular actualVacuum)
    (hReserve : P.activities.KBound pK vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1)
    (x : X) (U : Config G n) :
    Poly.price w (forcedClusterError (T.leaf x) U) ≤
      ((Fintype.card V : ℝ) * (κ * forcedPrice)) *
        Real.exp (-min (flagRate pK) (flagRate p) * (flags P.p.threshold U).card) := by
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
  exact ForcedCover.cluster_difference B w h.radii hP U k a
    (fun i => (hk i).1) ha (fun i => (hk i).2 U) hMark γ M hHit hMarked

/-- The original vacuum bound is already sufficient, retaining the smaller
of the original and marked support rates. -/
theorem FullBudget.forced_cluster_price
    (h : FullBudget p T w κ regularPrice forcedPrice)
    {regular vacuum : ℝ} (hP : P.activities.Valid P.p regular vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1)
    (x : X) (U : Config G n) :
    Poly.price w (forcedClusterError (T.leaf x) U) ≤
      ((Fintype.card V : ℝ) * (κ * forcedPrice)) *
        Real.exp (-min (flagRate P.p) (flagRate p) * (flags P.p.threshold U).card) :=
  h.forced_cluster_price_of_reserve hP hP.boundK hSmall x U

/-- The native vacuum reserve permits the full marked support rate, without
equating the reserved norm point with the carrier's physical point. -/
theorem FullBudget.forced_cluster_price_reserved
    (h : FullBudget p T w κ regularPrice forcedPrice)
    {regular actualVacuum vacuum : ℝ}
    (hP : P.activities.Valid P.p regular actualVacuum)
    (hReserve : P.activities.KBound p vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1)
    (x : X) (U : Config G n) :
    Poly.price w (forcedClusterError (T.leaf x) U) ≤
      ((Fintype.card V : ℝ) * (κ * forcedPrice)) *
        Real.exp (-flagRate p * (flags P.p.threshold U).card) := by
  simpa only [min_self] using h.forced_cluster_price_of_reserve hP hReserve hSmall x U

omit [Fintype V] in
/-- With no flags the sole admissible packet is empty, so the complete
forced numerator vanishes exactly, without a norm or smallness premise. -/
theorem forcedClusterError_zero (d : Deck R P) (U : Config G n)
    (hFlags : flags P.p.threshold U = ∅) : forcedClusterError d U = 0 := by
  have hCluster : d.contents.cluster U = 1 := by
    unfold Bands.cluster
    rw [tsum_eq_single ∅]
    · have h : P.activities.admissible P.p U ∅ := by
        simp [Activities.admissible, hFlags]
      simp [Bands.packet, h]
    intro s hs
    have hNot : ¬P.activities.admissible P.p U s := by
      intro h
      obtain ⟨i, hi⟩ := nonempty_iff_ne_empty.mpr hs
      obtain ⟨y, hy⟩ := (P.activities.forced i).inventory_ne
      have hyFlags : y ∈ flags P.p.threshold U :=
        h.2 ▸ mem_biUnion.mpr ⟨i, hi, hy⟩
      simp only [hFlags, notMem_empty] at hyFlags
    simp only [Bands.packet, if_neg hNot]
  unfold forcedClusterError
  rw [hCluster, P.activities.gas_one P.p hFlags]
  simp

/-- The same numerator price also records its exact support on flagged
fields; all weights are independent of the chosen test parameter. -/
theorem FullBudget.forced_cluster_price_flagged
    (h : FullBudget p T w κ regularPrice forcedPrice)
    {regular vacuum : ℝ} (hP : P.activities.Valid P.p regular vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1)
    (x : X) (U : Config G n) :
    Poly.price w (forcedClusterError (T.leaf x) U) ≤
      if flags P.p.threshold U = ∅ then 0 else
        ((Fintype.card V : ℝ) * (κ * forcedPrice)) *
          Real.exp (-min (flagRate P.p) (flagRate p) * (flags P.p.threshold U).card) := by
  split_ifs with hFlags
  · rw [forcedClusterError_zero (T.leaf x) U hFlags, Poly.zero_price]
  exact h.forced_cluster_price hP hSmall x U

/-- Restore the original physical coefficients and product kernel envelope.
Only the marker radii change coordinates; the carrier and flag set do not. -/
theorem RelativeBudget.forced_cluster_price_reserved
    {cost : V → ℝ}
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v) {regular actualVacuum vacuum : ℝ}
    (hP : P.activities.Valid P.p regular actualVacuum)
    (hReserve : P.activities.KBound p vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1)
    (x : X) (U : Config G n) :
    Poly.price (fun v => w v / cost v) (forcedClusterError (T.leaf x) U) ≤
      ((Fintype.card V : ℝ) * (κ * forcedPrice)) *
        Real.exp (-flagRate p * (flags P.p.threshold U).card) := by
  rw [forcedClusterError_product_price T cost hcost w x U]
  exact h.budget.forced_cluster_price_reserved hP hReserve hSmall x U

/-- The physical product-envelope bound retains exact zero on unflagged
fields, ready for a normalized integral without a spurious constant term. -/
theorem RelativeBudget.forced_cluster_price_reserved_flagged
    {cost : V → ℝ}
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v) {regular actualVacuum vacuum : ℝ}
    (hP : P.activities.Valid P.p regular actualVacuum)
    (hReserve : P.activities.KBound p vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1)
    (x : X) (U : Config G n) :
    Poly.price (fun v => w v / cost v) (forcedClusterError (T.leaf x) U) ≤
      if flags P.p.threshold U = ∅ then 0 else
        ((Fintype.card V : ℝ) * (κ * forcedPrice)) *
          Real.exp (-flagRate p * (flags P.p.threshold U).card) := by
  split_ifs with hFlags
  · rw [forcedClusterError_zero (T.leaf x) U hFlags, Poly.zero_price]
  exact h.forced_cluster_price_reserved hcost hP hReserve hSmall x U

end YM.Integration.LocalComparison
