import YM.Integration.ActualRunPacketRetuning

/-! Freeze the explicit coupling powers at one physical value, before
choosing a formal input. All original Option rows and full nonlinear field
functions remain. The original Paid receipt is transferred with no loss. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualPacketCouplingFreeze
open Lattice Wilson RG Marker
open Comparison.Density.RenderM LocalComparison ActualRunPacketRetuning
open scoped BigOperators

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V]
  {D : V → ComparisonDensity.Address.Orbit} {S : Census V}

private def zeroPower (P : MarkedPackets D G n S) : MarkedPackets D G n S :=
  { P with
    power := fun _ => 0
    powerCap := 0
    power_bounded := fun _ _ _ => by simp
    nonnegative_grade := fun _ _ _ => by simp }

private theorem zeroPower_term (P : MarkedPackets D G n S) (g : ℝ)
    (x : TestSpace D) (U : Config G n) (i : ℕ) :
    (zeroPower P).term x g U i = P.term x 1 U i := by
  cases h : P.packet i <;>
    simp only [MarkedPackets.term, zeroPower, h, zpow_zero, Complex.ofReal_one,
      one_zpow, one_mul]

private theorem zeroPower_read [Fintype V] (P : MarkedPackets D G n S) (g : ℝ)
    (x : TestSpace D) (U : Config G n) :
    (zeroPower P).read x g U = P.read x 1 U := by
  apply tsum_congr
  intro i
  exact congrArg (Poly.send (P.mode i)) (zeroPower_term P g x U i)

private theorem zeroPower_paid (P : MarkedPackets D G n S) (g : ℝ)
    {B : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {width budget : ℝ} {coverOffset coverSlope : ℕ}
    (hP : P.Paid B address region w 1 width budget coverOffset coverSlope) :
    (zeroPower P).Paid B address region w g width budget coverOffset coverSlope := by
  refine
    { width_pos := hP.width_pos
      positive := hP.positive
      coefficient := hP.coefficient
      paths := hP.paths
      addresses := hP.addresses
      symmetry := hP.symmetry
      reads := hP.reads
      multilinear := hP.multilinear
      roots := ?_
      cover := hP.cover
      width_reserved := hP.width_reserved }
  intro v
  convert hP.roots v using 1
  funext i
  dsimp only [zeroPower]
  split_ifs
  · cases P.packet i with
    | none => rfl
    | some T =>
      simp only [zpow_zero, Complex.ofReal_one, one_zpow, norm_one, mul_one]
  · rfl

def freeze (P : MarkedPackets D G n S) (physical : ℝ) : MarkedPackets D G n S :=
  zeroPower (retune P physical)

/-- The exact original token is multiplied by its physical coupling power. -/
theorem freeze_packet (P : MarkedPackets D G n S) (physical : ℝ) (i : ℕ) :
    (freeze P physical).packet i =
      (P.packet i).map (scaleToken ((physical : ℂ) ^ P.power i)) := rfl

/-- The original layout and rank cap remain; every explicit power is zero. -/
theorem freeze_layout (P : MarkedPackets D G n S) (physical : ℝ) :
    (freeze P physical).mode = P.mode ∧
    (freeze P physical).rank = P.rank ∧
    (freeze P physical).rankCap = P.rankCap ∧
    (freeze P physical).power = (fun _ => 0) ∧
    (freeze P physical).powerCap = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Exact full-function identity for all evaluation couplings, including zero. -/
theorem freeze_read [Fintype V] (P : MarkedPackets D G n S)
    (physical g : ℝ) (x : TestSpace D) (U : Config G n) :
    (freeze P physical).read x g U = P.read x physical U := by
  change (zeroPower (retune P physical)).read x g U = _
  rw [zeroPower_read, retune_read, mul_one]

/-- The old physical Paid bill pays the frozen packet at every coupling. -/
theorem freeze_paid (P : MarkedPackets D G n S) (physical g : ℝ)
    {B : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {width budget : ℝ} {coverOffset coverSlope : ℕ}
    (hP : P.Paid B address region w physical width budget coverOffset coverSlope) :
    (freeze P physical).Paid B address region w g width budget coverOffset coverSlope := by
  apply zeroPower_paid
  apply retune_paid
  simpa only [mul_one] using hP

end YM.Integration.ActualPacketCouplingFreeze
end
