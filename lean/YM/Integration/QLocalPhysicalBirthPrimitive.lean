import YM.Integration.QLocalPhysicalBirthTowing
import YM.Integration.QLocalBarcodeIncidence
import YM.Extra.ITERATION_NO_LOSS.Sums

/-! The physical primitive cluster input is paid by the genuine singleton
regular leaf exposure and the existing compulsory inventory of the same Run.
There is no factor for the size of the torus or the number of marked modes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalPhysicalBirthPrimitive
open Function Finset Lattice Wilson RG Marker FVA1
open Extra.Histories Extra.Trajectories PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.Replicum MergeProof.Replicums MergeProof.Ribbon
open Packets Push.GridApprox.Nil Push.AbsoluteSums Extra.Iteration
open scoped BigOperators Classical

private lemma subseries {ι κ : Type*} (j : ι ↪ κ) {f : κ → ℝ} {c : ℝ}
    (h : SumBudget f c) : SumBudget (f ∘ j) c :=
  budget_of_sum (fun i => h.1 (j i)) fun s => by
    simpa [Finset.sum_map, Function.comp_def] using budget_sum h (s.map j)

private lemma posted {ι κ : Type*} [Fintype ι] [Fintype κ] (q : ι → κ)
    {f : ι → ℝ} {c : ℝ} (h : SumBudget f c) :
    SumBudget (fun z : ι × κ => if z.2 = q z.1 then f z.1 else 0) c := by
  refine ⟨fun z => ite_nonneg (h.1 _) le_rfl, Summable.of_finite, ?_⟩
  rw [tsum_fintype,Fintype.sum_prod_type]
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true, tsum_fintype] using h.2.2

private lemma twice {ι : Type*} [Fintype ι] {f : ι → ℝ} {c : ℝ} (h : SumBudget f c) :
    SumBudget (fun z : ι × Bool => f z.1) (c+c) := by
  refine ⟨fun z => h.1 _, Summable.of_finite, ?_⟩
  rw [tsum_fintype,Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool]
  rw [Finset.sum_add_distrib]
  simpa only [tsum_fintype] using add_le_add h.2.2 h.2.2

variable {G : Gauge} (R : Run G) (N p L : ℕ) {V : Type} [DecidableEq V] [Fintype V]
  (o : Positions V (R.family.side L p)) (d : V → ℕ) (v : ∀ i, R.family.label (d i))
local notation "P₀" => R.family.path.rep N p L
local notation "Z₀" => ActualRunUnmaskedPartners.actualInput R N p L o d v
local notation "D₀" => NativeCaptionDeck.Input.deck Z₀ (BudgetPoint.threshold (Rep.p P₀))
local notation "M₀" => Replicum.Aged 0 V
local notation "X₀" => fun i => ActualRunPhysicalPages.cover R p L (d i) o i
local notation "u₀" => fun i => ActualRunUnmaskedPartners.globalPrice R N p L (d i) (v i)

private lemma firing (i : V) : (Z₀).cover ((Z₀).region i) ((M₀).fire (i,0)) = (Z₀).region i := by
  apply Finset.union_eq_left.mpr
  simpa [Replicum.span,Census.fire,NativeCaptionDeck.Input.focus,ActualRunUnmaskedPartners.actualInput]
    using (show o.origin i ∈ (X₀) i from Finset.mem_union_right _ (o.mem i))

private lemma silence (s : Support (R.family.side L p)) : (Z₀).cover s (M₀).quiet = s := by
  simp [NativeCaptionDeck.Input.cover,Replicum.span,Census.quiet]

/-- Charge every actual primitive input. The two recorded health flags give
at most two copies of a regular charge, and each compulsory barcode is priced
only at its original quiet input. -/
theorem incidence (w : V → ℝ) (b : ℕ → ℝ) {a r c : ℝ}
    (hR : Ac.Hit (X₀) (P₀).p.B (fun i => w i * (u₀) i) a r)
    (hK : Ac.Hit Prod.fst (P₀).p.B (QLocalPhysicalBirthInvoice.barcodePrice (P₀).activities b) a c) :
    Ac.Hit (D₀).cover (P₀).p.B (QLocalPhysicalBirthTowing.markedToll R N p L o d v b w) a (r+r+c) := by
  intro x
  let f (i : (Z₀).Seed ⊕ (Z₀).ForcedKey) := if x ∈ (D₀).cover i then
    QLocalPhysicalBirthTowing.markedToll R N p L o d v b w i *
      Real.exp (a * coverNumber (P₀).p.B ((D₀).cover i)) else 0
  change SumBudget f (r+r+c)
  apply Cost.sum
  · let A (i : V) := if x ∈ (X₀) i then w i * (u₀) i * Real.exp (a * coverNumber (P₀).p.B ((X₀) i)) else 0
    let T (z : V × (M₀).Mode) := if z.2 = (M₀).fire (z.1,0) then A z.1 else 0
    have hA : SumBudget A r := hR x
    have hT : SumBudget T r := by
      convert posted (fun i => (M₀).fire (i,0)) hA using 1
      funext z
      by_cases hq : z.2 = (M₀).fire (z.1,0) <;> simp [T,hq]
    have hS := twice (subseries (Function.Embedding.subtype _) hT : SumBudget (fun j : (Z₀).RegularKey => T j.val) r)
    convert hS using 1
    funext j
    rcases j with ⟨⟨⟨i,q⟩,hp⟩,flag⟩
    change (if x ∈ (Z₀).cover ((Z₀).region i) q then Poly.toll (fun j : Replicum.Name 0 V => w j.1) q *
      (if q = (M₀).fire (i,0) then (u₀) i else 0) *
      Real.exp (a * coverNumber (P₀).p.B ((Z₀).cover ((Z₀).region i) q)) else 0) =
      if q = (M₀).fire (i,0) then A i else 0
    by_cases hq : q = (M₀).fire (i,0)
    · subst q
      simp only [firing R N p L o d v i]
      simp [A,Poly.toll,Census.fire,ActualRunUnmaskedPartners.actualInput]
    · simp [hq]
  · let B (s : Box (R.family.side L p)) := if x ∈ s.1 then
      QLocalPhysicalBirthInvoice.barcodePrice (P₀).activities b s * Real.exp (a * coverNumber (P₀).p.B s.1) else 0
    let T (z : Box (R.family.side L p) × (M₀).Mode) := if z.2 = (M₀).quiet then B z.1 else 0
    have hB : SumBudget B c := hK x
    have hT : SumBudget T c := by
      convert posted (fun _ => (M₀).quiet) hB using 1
      funext z
      by_cases hq : z.2 = (M₀).quiet <;> simp [T,hq]
    have hu := (subseries (Function.Embedding.subtype _) hT : SumBudget (fun j : (Z₀).ForcedKey => T j.val) c)
    convert hu using 1
    funext j
    rcases j with ⟨⟨s,q⟩,hp⟩
    change (if x ∈ (Z₀).cover s.1 q then Poly.toll (fun j : Replicum.Name 0 V => w j.1) q *
      (if q = (M₀).quiet then QLocalPhysicalBirthInvoice.barcodePrice (P₀).activities b s else 0) *
      Real.exp (a * coverNumber (P₀).p.B ((Z₀).cover s.1 q)) else 0) = _
    by_cases hq : q = (M₀).quiet
    · subst q
      simp only [silence R N p L o d v s.1]
      simp [T,B,Poly.toll,Census.quiet]
    · simp [hq,T]

/-- The selected original physical forced allowance and the untested regular
leaf bill buy the actual nonlinear all-mode output. -/
theorem delivery (hL : L ≤ N) (href : ∀ i, R.family.ref (d i) ≤ L)
    (w : V → ℝ) (hw : ∀ i, 0 < w i) {a e r : ℝ} (ha : 0 ≤ a) (he : a+e ≤ (P₀).p.supportExponent)
    (hR : Ac.Hit (X₀) (P₀).p.B (fun i => w i * (u₀) i) (a+e) r)
    (hsmall : (((P₀).p.B + (P₀).p.B + 1 : ℕ) : ℝ)^4 * (r+r+R.family.path.levels.clock.forcedAllowance L) ≤ e) :
    ∃ B : Box (R.family.side L p) → Sheet (Ribbon.Bud V), (∀ s, 0 ≤ B s) ∧
      (∀ s U q, ‖(ActualRunUnmaskedPartners.actualCorrection R N p L o d v s U).part q‖ ≤ B s q) ∧
      Ac.Hit Prod.fst (P₀).p.B (fun s => wordsPrice w (B s)) a
        (Real.exp (r+r+R.family.path.levels.clock.forcedAllowance L)-1) := by
  obtain ⟨b,hs,_,hb,hK⟩ := QLocalBarcodeIncidence.physical R N p L hL
  exact QLocalPhysicalBirthTowing.sheet R N p L o d v hL href b hs hb w hw ha
    (incidence R N p L o d v w b hR (hK _ he)) hsmall

end YM.Integration.QLocalPhysicalBirthPrimitive
end
