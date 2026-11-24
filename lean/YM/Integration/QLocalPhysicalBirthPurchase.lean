import YM.Integration.QLocalPhysicalBirthWeights
import YM.Integration.QLocalPhysicalBirthPrimitive
import YM.Integration.QLocalPhysicalBirthClock

/-! A nonzero preselected physical scale radius buys the literal full startup
menu and its original mixed outgoing corrections uniformly over later periods,
cutoffs, origins and independent tests on the stated cover ceiling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalPhysicalBirthPurchase
open Function Filter Finset Lattice Wilson RG Marker FVA1
open Extra.Histories Extra.Trajectories PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.Replicum MergeProof.Replicums MergeProof.Ribbon
open Packets Push.GridApprox.Nil Push.AbsoluteSums
open scoped BigOperators Classical Topology

private theorem weaker {ι : Type*} {n : Side} {X : ι → Support n} {B : ℕ} {f : ι → ℝ} {a e c : ℝ}
    (hf : ∀ i, 0 ≤ f i) (ha : a ≤ e) (h : Ac.Hit X B f e c) : Ac.Hit X B f a c := by
  intro x
  apply budget_mono (h x)
  · intro i
    split
    · exact mul_nonneg (hf i) (Real.exp_nonneg _)
    · rfl
  · intro i
    split
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _))) (hf i)
    · rfl

variable {G : Gauge} (R : Run G) (L : ℕ)
local notation "P₀" => R.family.path.levels.budget L
local notation "λ₀" => Push.Local.hitWidth (P₀)
local notation "κ₀" => R.family.path.levels.clock.forcedAllowance L
local notation "ρ₀" => QLocalPhysicalBirthClock.reserve R

def debit (τ : ℝ) := min τ ((ρ₀)/(4*(λ₀)))

private theorem width_pos : 0 < (λ₀) := by unfold Push.Local.hitWidth; positivity

theorem debit_pos {τ : ℝ} (hτ : 0 < τ) : 0 < debit R L τ :=
  lt_min hτ (div_pos (QLocalPhysicalBirthClock.positive R) (mul_pos (by norm_num) (width_pos R L)))

theorem within {τ : ℝ} (h : (λ₀)*(κ₀) ≤ (ρ₀)/2) :
    (λ₀)*(debit R L τ+debit R L τ+(κ₀)) ≤ (ρ₀) := by
  have hwidth := width_pos R L
  have hr : debit R L τ ≤ (ρ₀)/(4*(λ₀)) := min_le_right _ _
  have hpaid := (le_div_iff₀ (show 0 < 4*(λ₀) from by positivity)).mp hr
  nlinarith

variable {V : Type} [DecidableEq V] [Fintype V]

theorem prepaid (hG : G.Simple) : ∀ᶠ L : ℕ in atTop,
    ∀ (d : V → ℕ) (v : ∀ i, R.family.label (d i)), (∀ i, R.family.ref (d i) ≤ L) →
    ∀ (C τ : ℝ), 0 < τ →
    let r := debit R L τ
    let w := QLocalPhysicalBirthWeights.weight R L d v C r
    (0 < r ∧ r ≤ τ ∧ ∀ i, 0 < w i) ∧
    ∀ (N p : ℕ) (hL : L ≤ N) (o : Positions V (R.family.side L p)),
      (∀ i, (coverNumber (R.family.path.levels.budget L).B (ActualRunPhysicalPages.cover R p L (d i) o i) : ℝ) ≤ C) →
      ∃ B : Box (R.family.side L p) → Sheet (Ribbon.Bud V),
        (∀ s, 0 ≤ B s) ∧
        (∀ s U q, ‖(ActualRunUnmaskedPartners.actualCorrection R N p L o d v s U).part q‖ ≤ B s q) ∧
        Ac.Hit Prod.fst (R.family.path.rep N p L).p.B (fun s => wordsPrice w (B s))
          ((R.family.path.rep N p L).p.supportExponent-4) (Real.exp (r+r+R.family.path.levels.clock.forcedAllowance L)-1) ∧
        MenuSafe (ActualRunFullPages.pages R hG N p L hL o d v) o
          (ActualRunFullPages.prices R p L o d v B) w (r+(Real.exp (r+r+R.family.path.levels.clock.forcedAllowance L)-1)) := by
  filter_upwards [QLocalPhysicalBirthClock.purchased R hG] with L hgas
  intro d v href C τ hτ
  let r := debit R L τ
  let w := QLocalPhysicalBirthWeights.weight R L d v C r
  have hr : 0 < r := debit_pos R L hτ
  have hw (i : V) : 0 < w i := QLocalPhysicalBirthWeights.positive R L d v C hr href i
  refine ⟨⟨hr,min_le_left _ _,hw⟩,?_⟩
  intro N p hL o hC
  let P := R.family.path.rep N p L
  have hp : P.p = R.family.path.levels.budget L := (R.makes.wilson.represents N p L hL).vac
  let a := max 0 (P.p.supportExponent-4)
  have he : a + QLocalPhysicalBirthClock.reserve R ≤ P.p.supportExponent := by
    simpa only [a,hp] using QLocalPhysicalBirthClock.permitted R L
  have expenses (e : ℝ) (h : e ≤ (R.family.path.levels.budget L).supportExponent) :=
    QLocalPhysicalBirthWeights.charges R L d v N p hL href o hr h hC
  have hinc := (expenses _ (he.trans_eq (congrArg BudgetPoint.supportExponent hp))).1
  have hsize : (((P.p.B + P.p.B + 1 : ℕ) : ℝ)^4) * (r+r+R.family.path.levels.clock.forcedAllowance L) ≤
      QLocalPhysicalBirthClock.reserve R := by
    rw [hp]
    simpa only [Push.Local.hitWidth,Nat.cast_pow] using within R L (τ := τ) hgas
  obtain ⟨B,hB,hcoeff,hforce⟩ := QLocalPhysicalBirthPrimitive.delivery R N p L o d v hL href w hw
    (le_max_left _ _ : 0 ≤ a) he hinc hsize
  have hroot (s : Box (R.family.side L p)) : 0 ≤ wordsPrice w (B s) :=
    sum_nonneg fun q _ => mul_nonneg (Poly.worth hw q).le (hB s q)
  have hforce' := weaker hroot (le_max_right 0 (P.p.supportExponent-4)) hforce
  have ha : P.p.supportExponent-4 ≤ (R.family.path.levels.budget L).supportExponent := by rw [hp]; linarith
  exact ⟨B,hB,hcoeff,hforce',ActualRunFullPages.menuSafe R hG N p L hL o d v href B hB hcoeff w hw
    (expenses _ ha).2 hforce'⟩

end YM.Integration.QLocalPhysicalBirthPurchase
end
