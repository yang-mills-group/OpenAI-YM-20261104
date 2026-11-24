import YM.GapsI.Many.Seat
import YM.MergeProof.Garnish
import YM.MergeProof.Grant
import YM.MergeProof.Tally
import YM.MergeProof.Stretch
import YM.Push.ABSOLUTE_SUMS.Product

/-!
The full forced half of an Overlay presentation, including the original
quiet activities. Every countable entry and every original support/inventory
barcode is retained. The marked and quiet receipts meet at one explicit
cover exponent; their prices add without a volume factor.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.OverlayForcedBarcode
open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay
open MergeProof MergeProof.Accent Push Push.AbsoluteSums
open scoped Classical BigOperators

private theorem towed_add {V I Y : Type*} [DecidableEq V] {B : Census V}
    {n : Side} {w : V → ℝ} {s : I → Support n}
    {F H : I → Y → Poly B} {M : ℕ} {e a b : ℝ}
    (hF : Towed w s F M e a) (hH : Towed w s H M e b) :
    Towed w s (fun i U => F i U + H i U) M e (a + b) := by
  obtain ⟨f, hf, hHitF, hLociF⟩ := hF
  obtain ⟨g, hg, hHitG, hLociG⟩ := hH
  refine ⟨fun i => f i + g i, hf.add hg, ?_, ?_⟩
  · intro x
    convert Extra.Multi.Budget.plus (hHitF x) (hHitG x) using 1
    funext i
    split_ifs <;> ring
  · intro i
    obtain ⟨v, hv, hboundV, hpriceV⟩ := hLociF i
    obtain ⟨z, hz, hboundZ, hpriceZ⟩ := hLociG i
    refine ⟨fun q => v q + z q, fun q => add_nonneg (hv q) (hz q), ?_, ?_⟩
    · intro U q
      exact (norm_add_le _ _).trans (add_le_add (hboundV U q) (hboundZ U q))
    · simpa only [GridApprox.Nil.wordsPrice, mul_add, sum_add_distrib]
        using add_le_add hpriceV hpriceZ

private theorem tally_fst {Y V : Type*} [DecidableEq V] {B : Census V}
    (F : ℕ × ℕ → Y → Poly B) (i : ℕ) (U : Y) :
    tally Prod.fst F i U = ∑' j, F (i, j) U := by
  let e : ℕ ≃ {p : ℕ × ℕ // p.1 = i} := {
    toFun := fun j => ⟨(i, j), rfl⟩
    invFun := fun p => p.val.2
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨⟨k, j⟩, h⟩
      cases h
      rfl }
  exact (e.tsum_eq (fun p => F p.val U)).symm

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V]
    {B : Census V} {P : Rep G n} (A : Overlay.Bands B P)

/-- This is the complete original forced family, including its quiet term. -/
def full : Box n → Config G n → Poly B :=
  tally (barcode P.activities) A.each

variable {w : V → ℝ} {b u δ κ σ : ℝ}
    (hGlow : GapsI.Seat.Glow A w b u) (hw : ∀ i, 0 < w i)
include hGlow hw

/-- All marked entries receive one coefficient envelope from the native Glow. -/
theorem tagged_towed (hb : 0 ≤ b) :
    Towed w (Extra.Multi.forced P)
      (fun i U => A.tagged i.1 i.2 U) P.p.B b u := by
  obtain ⟨g, hg, hHit⟩ := hGlow.posts
  have hg0 i : 0 ≤ g i := (norm_nonneg _).trans (hg i 1)
  let c i := Poly.toll w (Extra.Multi.tags A i) * g i
  have hc i : 0 ≤ c i := mul_nonneg (Poly.worth hw _).le (hg0 i)
  have hC : Ac.Hit (Extra.Multi.forced P) P.p.B c b u := hHit
  have hs := Product.everyone_ne (Extra.Multi.forced P) P.p.B hc
    (fun i _ => (P.activities.forced i.1).inventory_ne.mono
      (P.activities.forced i.1).inventory_sup) hC
  refine ⟨c, hs.2.1.of_nonneg_of_le hc (fun i =>
    le_mul_of_one_le_right (hc i)
      (Real.one_le_exp (mul_nonneg hb (by positivity)))), hC, ?_⟩
  intro i
  exact satin (A.entries i.1 i.2) (A.marks i.1 i.2) (g i) (hg0 i) (hg i)

theorem tagged_summable (hb : 0 ≤ b) (i : ℕ) (U : Config G n) :
    Summable (fun j => A.tagged i j U) := by
  exact ((tagged_towed A hGlow hw hb).repair hw U).2.comp_injective
    (i := fun j : ℕ => (i, j))
    (fun _ _ h => congrArg Prod.snd h)

private theorem marked_rows_towed (hb : 0 ≤ b) :
    Towed w (fun i => (P.activities.forced i).support)
      (fun i U => ∑' j, A.tagged i j U) P.p.B b u := by
  have h := towing (r := fun i : ℕ => (P.activities.forced i).support)
    Prod.fst (fun i U => A.tagged i.1 i.2 U)
    (tagged_towed A hGlow hw hb) hw
  have he : tally Prod.fst (fun i U => A.tagged i.1 i.2 U) =
      (fun i U => ∑' j, A.tagged i j U) := by
    funext i U
    exact tally_fst _ i U
  rwa [he] at h

variable (hV : P.activities.Valid P.p δ κ)
include hV

omit hGlow hw in
private theorem quiet_rows_towed :
    Towed w (fun i => (P.activities.forced i).support)
      (fun i U => Poly.send B.quiet (P.activities.K i U : ℂ))
      P.p.B P.p.supportExponent κ := by
  obtain ⟨g, hg, hHit⟩ := hV.boundK
  refine ⟨g, Activities.summable_charge
    (fun i => (P.activities.forced i).inventory_ne.mono
      (P.activities.forced i).inventory_sup) (fun i => (hg i).1) hHit, ?_, ?_⟩
  · intro x
    convert hHit x using 1
    funext i
    unfold BudgetPoint.mass
    split_ifs <;> ring
  · intro i
    have h := satin (w := w) (fun U => (P.activities.K i U : ℂ)) B.quiet (g i)
      (hg i).1 (fun U => by simpa only [Complex.norm_real] using (hg i).2 U)
    simpa only [Poly.quiet_toll, one_mul] using h

/-- The original quiet allowance and the marked allowance meet at the same
explicit exponent. No countable label or degree is removed. -/
theorem each_towed (hσ : 0 ≤ σ) (hσb : σ ≤ b)
    (hσP : σ ≤ P.p.supportExponent) :
    Towed w (fun i => (P.activities.forced i).support) A.each
      P.p.B σ (κ + u) := by
  exact towed_add
    ((quiet_rows_towed hV).shrink hσP le_rfl hw)
    ((marked_rows_towed A hGlow hw (hσ.trans hσb)).shrink hσb le_rfl hw)

/-- Finite barcode aggregation preserves the exact sum of the original
quiet and marked prices, uniformly over every configuration. -/
theorem towed (hσ : 0 ≤ σ) (hσb : σ ≤ b)
    (hσP : σ ≤ P.p.supportExponent) :
    Towed w Prod.fst (full A) P.p.B σ (κ + u) :=
  towing (barcode P.activities) A.each (each_towed A hGlow hw hV hσ hσb hσP) hw

theorem part (hσ : 0 ≤ σ) (hσb : σ ≤ b)
    (hσP : σ ≤ P.p.supportExponent) (box : Box n) (U : Config G n) (q : B.Mode) :
    (full A box U).part q =
      ∑' i : {i : ℕ // barcode P.activities i = box}, (A.each i.val U).part q := by
  exact Poly.share (((each_towed A hGlow hw hV hσ hσb hσP).repair hw U).2.comp_injective
    Subtype.val_injective) q

/-- Literal equality with the existing Overlay cluster and its own barcode. -/
theorem field_eq (hσ : 0 ≤ σ) (hσb : σ ≤ b)
    (hσP : σ ≤ P.p.supportExponent) (U : Config G n) :
    A.cluster U = field (fun box => full A box U) (flags P.p.threshold U) := by
  exact (Accent.rock_out P.activities P.p U (fun i => A.each i U) hw
    ((each_towed A hGlow hw hV hσ hσb hσP).repair hw U).1).symm

variable (hA : A.Active)
include hA

omit hV in
theorem each_quiet (hb : 0 ≤ b) (i : ℕ) (U : Config G n) :
    (A.each i U).part B.quiet = (P.activities.K i U : ℂ) := by
  rw [Overlay.Bands.each, Poly.part_plus,
    Poly.share (tagged_summable A hGlow hw hb i U)]
  have hz (j : ℕ) : (A.tagged i j U).part B.quiet = 0 := by
    rw [Overlay.Bands.tagged, Poly.part_send, if_neg]
    intro he
    exact (hA.occurs i j).ne_empty (congrArg Subtype.val he.symm)
  simp only [Poly.part_send, ↓reduceIte, hz, tsum_zero, add_zero]

variable [Fintype V]

theorem each_flow (hb : 0 ≤ b) (i : ℕ) :
    Flow A.origins (barcode P.activities i) (A.each i) P.p.threshold := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro U W hUW hFlags
    unfold Overlay.Bands.each
    rw [hV.forced.reads i U W hUW hFlags]
    congr 1
    exact tsum_congr (fun j => congrArg (Poly.send (A.marks i j))
      (hA.inspects i j U W hUW hFlags))
  · intro g U
    unfold Overlay.Bands.each
    rw [hV.forced.sym i g U]
    congr 1
    exact tsum_congr (fun j => congrArg (Poly.send (A.marks i j)) (hA.invi i j g U))
  · intro q
    exact (Poly.part_cont q).measurable.comp
      (((Overlay.Bands.sends B.quiet).measurable.comp
        (Complex.continuous_ofReal.measurable.comp (hV.forced.meas i))).add
        (Measurable.tsum (fun j =>
          (Overlay.Bands.sends (A.marks i j)).measurable.comp (hA.meas i j))))
  · intro U
    apply GridApprox.Nil.scope_plus
      (GridApprox.Nil.scope_send _ _ _ (by simp [Census.quiet]))
    intro q hq
    rw [Poly.share (tagged_summable A hGlow hw hb i U)]
    apply (tsum_congr _).trans tsum_zero
    intro j
    by_cases hj : A.entries i j = 0
    · simp only [Overlay.Bands.tagged, hj, Pi.zero_apply, Poly.send_zero, Poly.part_nil]
    exact GridApprox.Nil.scope_send _ (A.marks i j) _
      (fun _ h => hA.retained i j hj _ h) q hq
  · intro U hu
    have he : (P.activities.forced i).eligible P.p.threshold U := by
      by_contra hn
      apply hu
      have hk : P.activities.K i U = 0 :=
        not_ne_iff.mp (mt (hV.forced.permit i U) hn)
      have hj (j : ℕ) : A.entries i j U = 0 :=
        not_ne_iff.mp (mt (hA.keeps i j U) hn)
      simp only [Overlay.Bands.each, hk, Complex.ofReal_zero, Poly.send_zero,
        Overlay.Bands.tagged, hj, tsum_zero, add_zero]
    exact ⟨he.1, (P.activities.forced i).inventory_ne, (P.activities.forced i).inventory_sup⟩

theorem flow (hσ : 0 ≤ σ) (hσb : σ ≤ b)
    (hσP : σ ≤ P.p.supportExponent) (box : Box n) :
    Flow A.origins box (full A box) P.p.threshold :=
  transitK (barcode P.activities) (r := id)
    (each_flow A hGlow hw hV hA (hσ.trans hσb))
    (fun U => ((each_towed A hGlow hw hV hσ hσb hσP).repair hw U).2) box

omit [Fintype V] in
/-- The original unmarked K profile survives, including its countable sum. -/
theorem quiet (hσ : 0 ≤ σ) (hσb : σ ≤ b)
    (hσP : σ ≤ P.p.supportExponent) (box : Box n) (U : Config G n) :
    (full A box U).part B.quiet =
      profile P.activities (fun i => Complex.ofReal ∘ P.activities.K i) box U := by
  rw [part A hGlow hw hV hσ hσb hσP]
  exact tsum_congr (fun i => each_quiet A hGlow hw hA (hσ.trans hσb) i.val U)

omit [Fintype V] in
/-- In particular, the full actual gas factor is retained by the field. -/
theorem field_quiet (hσ : 0 ≤ σ) (hσb : σ ≤ b)
    (hσP : σ ≤ P.p.supportExponent) (U : Config G n) :
    (field (fun box => full A box U) (flags P.p.threshold U)).part B.quiet =
      (P.activities.gas P.p U : ℂ) :=
  Accent.stage₀ P.activities P.p U (Accent.mass_crest P.activities hV U)
    (fun box => quiet A hGlow hw hV hA hσ hσb hσP box U)

end YM.Integration.OverlayForcedBarcode
