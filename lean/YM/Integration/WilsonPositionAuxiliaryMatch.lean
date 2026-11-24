import YM.Integration.WilsonPositionAuxiliaryMesh

/-! Hear the signed physical comparison on one auxiliary mesh per radius
and accuracy, retaining the original first-derivative seminorm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionAuxiliaryMatch
open Filter Function Finset Set
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.Fleet
open Lattice Wilson RG Source Extraction Table Spec OPE OPE.Orbits Climb RG17 Trace.Pilot PhysMS PhysicalNext.Repeat.Legato
open WilsonPositionSeparatedProfileMatching WilsonPositionFiniteMSBank
open scoped Topology BigOperators Classical
variable {G : Gauge} (Z : WilsonPrescription G) {hG : G.Simple}
    {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z hG T σ dial)
    {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → PhysMS.tower S)
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z

def booked (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (q : ℕ) : Prop :=
  ∀ ε > 0, ∀ᶠ r in trail, ∃ i ≥ WilsonPositionAuxiliaryMesh.floor Z.run q (θ r),
    ‖observed Z F J none d φ v r - finite Z (Z.run.step i) d φ v q (θ r)‖ ≤ ε*|θ r|^q

theorem from_cofinal (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (q : ℕ)
    (all : cofinal Z F J d φ v q) : booked Z F J d φ v q := by
  intro ε ep
  filter_upwards [all ε ep] with r often
  obtain ⟨i,h,late⟩ := (often.and_eventually (eventually_ge_atTop (WilsonPositionAuxiliaryMesh.floor Z.run q (θ r)))).exists
  exact ⟨i,late,h⟩

include H in
theorem measured (ν : ℝ) (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (q : ℕ)
    {Y : (Bel R.family.book).Hierarchy} (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (lead : Leading F J) (paid : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d)
    (X : Scaling S) (foundation : Foundation F reader) (realRate : Coupling G θ)
    (offered : booked Z F J d φ v q) : matchesThrough Z T F J ν d φ v q := by
  intro ε ep
  have ep' : 0 < ε/3 := by positivity
  obtain ⟨A,ap,price⟩ := compact Z H ν d n v q φ.hasCompactSupport φ.tsupport_subset
  obtain ⟨b,bp,cap⟩ := TestBudget.bound_fin φ
  have ready := (goesFront (XSpace.Expense.Stretched.runs Z.run)).eventually price
  obtain ⟨k,ready⟩ := eventually_atTop.1 ready
  have zero := realRate.conforms hG
  have lower := (WilsonPositionAuxiliaryMesh.grows Z.run q trail realRate.positive zero).eventually_ge_atTop k
  have shrinks : Tendsto (fun r => b*A*θ r) trail (𝓝 0) := by simpa using zero.const_mul (b*A)
  have phase := phases Z F J reader lead paid hG X foundation d φ v θ realRate ep' q
  filter_upwards [offered (ε/3) ep', lower, shrinks.eventually_lt_const ep', phase, realRate.positive,
    zero.eventually_lt_const zero_lt_one] with r hx past small viewers gt unit p
  obtain ⟨i,enrolled,physical⟩ := hx
  rw [abs_of_pos gt] at physical ⊢
  have bound := ready i (past.trans enrolled) φ (Subset.rfl) b cap (θ r) (by simpa only [abs_of_pos gt] using unit.le)
  have spatial := WilsonPositionAuxiliaryMesh.cost Z.run q gt enrolled
  have cash : ‖finite Z (Z.run.step i) d φ v q (θ r) - polynomial Z T ν d φ v q (θ r)‖ ≤ (ε/3)*(θ r)^q :=
    calc
      _ ≤ b*A*(Z.run.step i).spacing^MS.Tide.mildG := bound
      _ ≤ b*A*(θ r)^(q+1) := mul_le_mul_of_nonneg_left spatial (mul_nonneg bp.le ap.le)
      _ = (b*A*θ r)*(θ r)^q := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right small.le (pow_nonneg gt.le _)
  calc
    _ ≤ ‖observed Z F J p d φ v r - observed Z F J none d φ v r‖ +
        ‖observed Z F J none d φ v r - polynomial Z T ν d φ v q (θ r)‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ (ε/3)*(θ r)^q + (‖observed Z F J none d φ v r - finite Z (Z.run.step i) d φ v q (θ r)‖ +
        ‖finite Z (Z.run.step i) d φ v q (θ r) - polynomial Z T ν d φ v q (θ r)‖) :=
      add_le_add (viewers p) (norm_sub_le_norm_sub_add_norm_sub ..)
    _ ≤ (ε/3)*(θ r)^q + ((ε/3)*(θ r)^q + (ε/3)*(θ r)^q) := add_le_add le_rfl (add_le_add physical cash)
    _ = _ := by ring

end YM.Integration.WilsonPositionAuxiliaryMatch
