import YM.Integration.QLocalPhysicalBirthInvoice

/-! The original physical startup deck's small primitive support bill
produces one common outgoing support bill for the actual mixed correction,
including singleton modes. The zero-arity fibers retain each original mark.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalPhysicalBirthTowing
open Function Finset Lattice Wilson RG Marker FVA1
open Extra.Histories Extra.Trajectories PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.Replicum MergeProof.Replicums MergeProof.Ribbon
open Packets Push.GridApprox.Nil Push.AbsoluteSums
open scoped BigOperators Classical

variable {G : Gauge} (R : Run G) (N p L : ℕ) {V : Type} [DecidableEq V] [Fintype V]
  (o : Positions V (R.family.side L p)) (d : V → ℕ) (v : ∀ i, R.family.label (d i))
local notation "P₀" => R.family.path.rep N p L
local notation "Z₀" => ActualRunUnmaskedPartners.actualInput R N p L o d v
local notation "D₀" => NativeCaptionDeck.Input.deck Z₀ (BudgetPoint.threshold (Rep.p P₀))

/-- Actual marked input charge on one honest underlying native seed. -/
def markedToll (b : ℕ → ℝ) (w : V → ℝ) (i : (Z₀).Seed ⊕ (Z₀).ForcedKey) : ℝ :=
  Poly.toll (fun j : Replicum.Name 0 V => w j.1) ((D₀).mode_ i) *
    QLocalPhysicalBirthInvoice.toll R N p L o d v b i

theorem rated (b : ℕ → ℝ) (hs : Summable b) (hb : ∀ i U, ‖(P₀).activities.K i U‖ ≤ b i)
    (w : V → ℝ) {a g : ℝ}
    (h : Ac.Hit (D₀).cover (P₀).p.B (markedToll R N p L o d v b w) a g) :
    (D₀).Rated (fun j : Replicum.Name 0 V => w j.1) (P₀).p.B a g := by
  have ht := QLocalPhysicalBirthInvoice.toll_bound R N p L o d v b hs hb
  exact ⟨_, fun i => (norm_nonneg _).trans (ht i 1), ht, h⟩

/-- A small incidence bill for the primitive physical inputs gives the
original mixed outgoing sheet with a volume-independent `exp(g) - 1` total.
The charge and smallness hypotheses concern only the specified physical
input tariff, before regrouping or testing. -/
theorem sheet (hL : L ≤ N) (href : ∀ i, R.family.ref (d i) ≤ L)
    (b : ℕ → ℝ) (hs : Summable b) (hb : ∀ i U, ‖(P₀).activities.K i U‖ ≤ b i)
    (w : V → ℝ) (hw : ∀ i, 0 < w i) {a e g : ℝ} (ha : 0 ≤ a)
    (h : Ac.Hit (D₀).cover (P₀).p.B (markedToll R N p L o d v b w) (a+e) g)
    (hsmall : (((P₀).p.B + (P₀).p.B + 1 : ℕ) : ℝ)^4 * g ≤ e) :
    ∃ B : Box (R.family.side L p) → Sheet (Ribbon.Bud V), (∀ s, 0 ≤ B s) ∧
      (∀ s U q, ‖(ActualRunUnmaskedPartners.actualCorrection R N p L o d v s U).part q‖ ≤ B s q) ∧
      Ac.Hit Prod.fst (P₀).p.B (fun s => wordsPrice w (B s)) a (Real.exp g-1) := by
  let W := fun j : Replicum.Name 0 V => w j.1
  have hw₀ : ∀ j, 0 < W j := fun j => hw j.1
  have ha₀ := ActualRunUnmaskedPartners.actual_input_admitted R N p L o d v hL href
  have hWet := (Z₀).wet (P₀).p.threshold ha₀
  have hR := rated R N p L o d v b hs hb w h
  have hprod (i : V) : w i = ∏ j : Fin (0+1), W (i,j) := by simp [W]
  obtain ⟨_, cap, hinc, hcoeff⟩ := ((D₀).carries (P₀).p.threshold hWet W w a e g
    (P₀).p.B hR ha hw₀ hprod hsmall).2
  choose B hpos hB hmoney using hcoeff
  refine ⟨B, hpos, fun s U q => ?_, fun x => ?_⟩
  · by_cases hq : q = (Ribbon.Bud V).quiet
    · subst q
      rw [ActualRunUnmaskedPartners.actual_correction_quiet R N p L o d v hL href, norm_zero]
      exact hpos s _
    · have hz : (bar (P₀).activities (Ribbon.Bud V) U s).part q = 0 := by
        simp [bar, Poly.bead, Poly.part_send, hq]
      change ‖((Z₀).forcedOutput _ s U).part q - (bar (P₀).activities (Ribbon.Bud V) U s).part q‖ ≤ _
      rw [hz,sub_zero]
      exact hB s U q
  · apply budget_mono (hinc x)
    · intro s
      split
      · exact mul_nonneg (sum_nonneg fun q _ => mul_nonneg (Poly.worth hw q).le (hpos s q)) (Real.exp_nonneg _)
      · rfl
    · intro s
      split
      · exact mul_le_mul_of_nonneg_right (hmoney s) (Real.exp_nonneg _)
      · rfl

end YM.Integration.QLocalPhysicalBirthTowing
end
