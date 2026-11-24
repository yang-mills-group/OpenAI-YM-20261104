import YM.Integration.ActualRunFullPages

/-! A concrete positive price for the unmasked forced correction at the
physical birth. Each original barcode keeps its own summable Nat fiber. A
marked coefficient is charged only to finite native branches with the
specified output box and precisely that surviving mode. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalPhysicalBirthInvoice
open Function Finset Lattice Wilson RG Marker FVA1 Push.GridApprox.Nil
open Extra.Histories Extra.Trajectories PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.Replicum MergeProof.Replicums MergeProof.Ribbon
open Packets Planned.GuardedAtom RG3.Held RG3.Script.Picnic
open scoped Topology BigOperators Classical

section Deck
variable {a : ℕ} {V I J : Type*} [DecidableEq V] [Fintype V] [DecidableEq I] [Fintype I]
  [DecidableEq J] [Fintype J] {n : Side} {G : Gauge} (D : Replicums.Deck a V I J G n)

/-- Native finite branch charge on a single original fused barcode and
one physical output coefficient. -/
def branchPrice (u : I ⊕ J → ℝ) (s : Box n) (q : (Ribbon.Bud V).Mode) : ℝ :=
  ∑ b : {i : D.Ink // D.fuse i.val = s},
    if q = D.quip (.inr b.val) then ∏ i ∈ b.val.val, u i else 0

theorem branch_nonneg (u : I ⊕ J → ℝ) (hu : ∀ i, 0 ≤ u i) (s : Box n) (q : (Ribbon.Bud V).Mode) :
    0 ≤ branchPrice D u s q :=
  sum_nonneg fun _ _ => ite_nonneg (prod_nonneg fun i _ => hu i) le_rfl

theorem branch_bound (u : I ⊕ J → ℝ) (hu : ∀ i U, ‖D.toll i U‖ ≤ u i)
    (t : ℝ) (U : Config G n) (s : Box n) (q : (Ribbon.Bud V).Mode) :
    ‖(D.clay t s U).part q‖ ≤ branchPrice D u s q := by
  unfold Replicums.Deck.clay tally branchPrice
  rw [Poly.share Summable.of_finite, tsum_fintype]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro b _
  change ‖(Poly.send (D.quip (.inr b.val)) (D.nectar t U b.val)).part q‖ ≤ _
  rw [Poly.part_send]
  by_cases hq : q = D.quip (.inr b.val)
  · simp only [if_pos hq]
    unfold Replicums.Deck.nectar
    split
    · change ‖∏ i ∈ b.val.val, D.toll i U‖ ≤ ∏ i ∈ b.val.val, u i
      rw [norm_prod]
      exact prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hu i U)
    · simpa using prod_nonneg (s := b.val.val) (fun i _ => (norm_nonneg _).trans (hu i U))
  · simp [hq]

end Deck

section Barcode
variable {G : Gauge} {n : Side} (A : Activities G n)

/-- The original summable K charge, restricted to precisely the retained
barcode's (possibly infinite) actual fiber. -/
def barcodePrice (b : ℕ → ℝ) (s : Box n) : ℝ :=
  ∑' i : {i : ℕ // barcode A i = s}, b i.val

theorem barcode_nonneg (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i) (s : Box n) :
    0 ≤ barcodePrice A b s := tsum_nonneg fun i => hb i.val

theorem barcode_bound (b : ℕ → ℝ) (hs : Summable b) (hb : ∀ i U, ‖A.K i U‖ ≤ b i)
    (s : Box n) (U : Config G n) :
    ‖profile A (fun i => Complex.ofReal ∘ A.K i) s U‖ ≤ barcodePrice A b s := by
  let f (i : {i : ℕ // barcode A i = s}) : ℂ := A.K i.val U
  have h (i) : ‖f i‖ ≤ b i.val := by simpa [f] using hb i.val U
  have hS : Summable (fun i : {i : ℕ // barcode A i = s} => b i.val) :=
    hs.comp_injective Subtype.val_injective
  have hF := Summable.of_nonneg_of_le (fun i => norm_nonneg (f i)) h hS
  exact (norm_tsum_le_tsum_norm hF).trans (hF.tsum_le_tsum h hS)

end Barcode

section Physical
variable {G : Gauge} (R : Run G) (N p L : ℕ) {V : Type} [DecidableEq V] [Fintype V]
  (o : Positions V (R.family.side L p)) (d : V → ℕ) (v : ∀ i, R.family.label (d i))
local notation "P₀" => R.family.path.rep N p L
local notation "Z₀" => ActualRunUnmaskedPartners.actualInput R N p L o d v
local notation "D₀" => NativeCaptionDeck.Input.deck Z₀ (BudgetPoint.threshold (Rep.p P₀))
local notation "marker" => Replicum.Aged 0 V

/-- The actual singleton leak price and the original real K barcode price,
with their exact native mode selectors. -/
def toll (b : ℕ → ℝ) : (Z₀).Seed ⊕ (Z₀).ForcedKey → ℝ :=
  Sum.elim
    (fun j => if j.1.val.2 = (marker).fire (j.1.val.1,0) then
      ActualRunUnmaskedPartners.globalPrice R N p L (d j.1.val.1) (v j.1.val.1) else 0)
    (fun j => if j.val.2 = (marker).quiet then barcodePrice (P₀).activities b j.val.1 else 0)

theorem toll_bound (b : ℕ → ℝ) (hs : Summable b) (hb : ∀ i U, ‖(P₀).activities.K i U‖ ≤ b i)
    (j : (Z₀).Seed ⊕ (Z₀).ForcedKey) (U : Config G (R.family.side L p)) :
    ‖(D₀).toll j U‖ ≤ toll R N p L o d v b j := by
  cases j with
  | inl j =>
    change ‖(Z₀).piece _ U j‖ ≤ _
    have hl := ActualRunUnmaskedPartners.actual_leak_price R N p L (d j.1.val.1)
      (v j.1.val.1) (o.origin j.1.val.1) (ActualRunPhysicalPages.cover R p L (d j.1.val.1) o j.1.val.1) U
    simp only [NativeCaptionDeck.Input.piece, ActualRunUnmaskedPartners.actualInput,
      ActualRunUnmaskedPartners.actualLeak, Poly.part_send, toll, Sum.elim_inl]
    split <;> split <;> simp_all only [norm_zero, le_refl]
    exact (norm_nonneg _).trans hl
  | inr j =>
    change ‖(Poly.send (marker).quiet _).part j.val.2‖ ≤ _
    simp only [Poly.part_send, toll, Sum.elim_inr]
    split
    · exact barcode_bound _ _ hs hb j.val.1 U
    · simp

/-- A positive sheet for the actual signed mixed forced correction, before
any chosen test, simultaneously on all configurations and coefficients. -/
theorem sheet (hL : L ≤ N) (href : ∀ i, R.family.ref (d i) ≤ L) :
    ∃ b : Box (R.family.side L p) → (Ribbon.Bud V).Mode → ℝ,
      (∀ s, 0 ≤ b s) ∧ ∀ s U q,
        ‖(ActualRunUnmaskedPartners.actualCorrection R N p L o d v s U).part q‖ ≤ b s q := by
  obtain ⟨b, hs, hb⟩ := Activities.K_total (R.makes.wilson.represents N p L hL).good.labels.boundK
  let u := toll R N p L o d v b
  have ht := toll_bound R N p L o d v b hs (fun i => (hb i).2)
  refine ⟨branchPrice D₀ u, fun s q => branch_nonneg _ u (fun i => (norm_nonneg _).trans (ht i 1)) s q, ?_⟩
  intro s U q
  by_cases hq : q = (Ribbon.Bud V).quiet
  · subst q
    rw [ActualRunUnmaskedPartners.actual_correction_quiet R N p L o d v hL href, norm_zero]
    exact branch_nonneg _ u (fun i => (norm_nonneg _).trans (ht i U)) _ _
  · have hz : (bar (P₀).activities (Ribbon.Bud V) U s).part q = 0 := by
      simp [bar, Poly.bead, Poly.part_send, hq]
    change ‖((Z₀).forcedOutput _ s U).part q - (bar (P₀).activities (Ribbon.Bud V) U s).part q‖ ≤ _
    rw [hz, sub_zero]
    exact branch_bound D₀ u ht _ U s q

/-- The genuine regular/forced startup page prices exist on the original
run, simultaneously for every configuration and every occupied page. -/
theorem entries (hG : G.Simple) (hL : L ≤ N) (href : ∀ i, R.family.ref (d i) ≤ L) :
    ∃ b : Box (R.family.side L p) → (Ribbon.Bud V).Mode → ℝ,
      ∀ j, (ActualRunFullPages.pages R hG N p L hL o d v j).Entry o
        (ActualRunFullPages.prices R p L o d v b j) := by
  obtain ⟨b, _, hb⟩ := sheet R N p L o d v hL href
  exact ⟨b, ActualRunFullPages.entries R hG N p L hL o d v href b hb⟩

end Physical
end YM.Integration.QLocalPhysicalBirthInvoice
end
