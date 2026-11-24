import YM.Integration.NativeRegulatorWilsonOpening

/-! Every finite stopped regulator coefficient comes from its own original
RG02 normalized local bank and the selected adjacent coupling change. -/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.NativeRegulatorActionStep

open Function Filter Lattice Wilson Precision RG Labels PhysicalNext.Repeat.Legato
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Moving
open Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Prim Diagram Diagram.Formal
open PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth
open Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2
open Integral Exterior Arm Marker Multi Pipeline Pipeline.See Period.Field Sound
open NativeFormalSharedCoupling NativeFormalPrescriptionAgreement NativeFormalRegulatorCollector
open WilsonLimitConstruction.FundedFormalEconomy NativeFormalDiagonalCollector PowerSeries
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {hG : G.Simple} {W : Bank R hG} {μ : ℝ}
  {P : MS.Land.Prescription (nativeDeck R)} {Z : branches R}
  {C : Lodge.Contract R (program R) Z} {A : table R} {g : G.ColorIndex}
  {I : Type} [Fintype I] [DecidableEq I] {i : I} {S : Marker.Census I}
  (T : Trial W μ P Z C A g i S)

local notation "𝓑" => C.profile (program R) Z R (schedule Z C T.order) (above Z C T.order)
local notation "periodSystem" => Period.Field.LodgeT.instance_real (program R) Z R C
  (schedule Z C T.order) (above Z C T.order)
local notation "𝓛" => Calibration.sheet T.calibrate
local notation "σ" => T.stop T.station

variable {n : ℕ} (v : Pegs.Motor (C.profile (program R) Z R (schedule Z C T.order) (above Z C T.order)) n T.station)
  (d : Fin n → ℕ) (u : (a : Fin n) → (R.family.labels.level (d a)).Index)
local notation "𝓐" => T.stamp.traces T.station n σ v d u
local notation "𝓕" => Figure.prop R (ProgramT.spend (program R) Z R C
  (schedule Z C T.order) (above Z C T.order) T.location T.station n v) d u
/-- The final edge ending at this station's selected stopping page. -/
def finalStep : Flap (𝓑).entire :=
  ⟨T.station,(𝓑).long T.station - 1, by
    have h : 0 < (𝓑).long T.station := Nat.mul_pos ((𝓑).life _) ((𝓑).life _)
    change (𝓑).long T.station - 1 < 2 * (𝓑).long T.station
    omega⟩

theorem finalStep_next : (finalStep T).next = (𝓑).stop.choose T.station := by
  have h : 0 < (𝓑).long T.station := Nat.mul_pos ((𝓑).life _) ((𝓑).life _)
  change (⟨T.station,(𝓑).long T.station-1+1,_⟩ : Page (𝓑).entire) = ⟨T.station,(𝓑).long T.station,_⟩
  congr 1

include v

variable (b : Flap (C.profile (program R) Z R (schedule Z C T.order) (above Z C T.order)).entire)
include b
local notation "Dir" => fieldDir G (R.family.side ((periodSystem).vol b.next) σ) 1
local notation:max "datum" a:max => Urban.buys R periodSystem S σ b 𝓐 a
local notation "prior" => T.stamp.menu.cloth b.prev

/-- The native marked transition, evaluated on the local normalized
coefficient bank of this Run. Every order from zero to the horizon participates. -/
theorem marked (x : Dir) {k : ℕ} (hk : k ≤ T.order) :
    See.prime periodSystem S i 𝓛 σ T.order T.stamp.menu 𝓐 (x := b.next) x k =
      Adjacent.born (fun j y => LocalFormal.runCoefficients R (datum y) T.order j (S.fire i))
        prior 0 T.order k x := by
  refine (Urban.readings T.order R periodSystem S i 𝓕 𝓛 σ b T.stamp.menu 𝓐
    (NativeRegulatorWilsonOpening.setup T v d u) x k hk).trans ?_
  apply congrArg (fun f : ℝ → ℂ => Comparison.RG02.Moving.Path.motion f k)
  funext t
  unfold Adjacent.ages Adjacent.cover
  apply congrArg (_ * ·)
  apply Finset.sum_congr rfl
  intro j hj
  apply congrArg (_ * ·)
  exact Urban.actualRun T.order R periodSystem S i σ b 𝓐 _ j (Finset.mem_range_succ_iff.mp hj)

/-- The unmarked transition is the centered native vacuum-action coefficient
on the same field, kernel, forest, physical time and trace. -/
theorem vacuum (x : Dir) {k : ℕ} (hk : k ≤ T.order) :
    See.visible S ((periodSystem).records (𝓑).desk R.family.path σ b.next).clip
        ((periodSystem).records (𝓑).desk R.family.path σ b.next).path
        (T.stamp.menu.cloth b.next) (𝓐 b.next) k x =
      Adjacent.born (fun j y => (datum y).vacuumAction (RunFormalChain.fromRun R) T.order j y)
        prior 0 T.order k x -
      Adjacent.born (fun j y => (datum y).vacuumAction (RunFormalChain.fromRun R) T.order j y)
        prior 0 T.order k 0 :=
  Urban.jetbook T.order R periodSystem S i 𝓕 𝓛 σ b T.stamp.menu 𝓐
    (NativeRegulatorWilsonOpening.setup T v d u) x k hk

/-- Exact normalized numerator/denominator reconstruction on the datum used
in each marked term of the stopped reading. -/
theorem normalized (x : Dir) :
    (datum x).denominator (RunFormalChain.fromRun R) T.order *
        (datum x).ordinary (RunFormalChain.fromRun R) T.order =
      (datum x).raw (RunFormalChain.fromRun R) T.order ∧
    Order.denominator ((datum x).ordinary (RunFormalChain.fromRun R) T.order) = 1 ∧
    Order.denominator ((datum x).markedLog (RunFormalChain.fromRun R) T.order) = 0 :=
  LocalFormal.run_normalization R (datum x) T.order

omit b

/-- The actual coefficient entering the finite regulator collector is measured
from the last local RG02 transition of its own selected construction. -/
theorem stopped {k : ℕ} (hk : k ≤ T.order) :
    coeff k (ProgramT.Ink (program R) Z R C (schedule Z C T.order) (above Z C T.order)
      T.calibrate T.order T.stop T.location S i T.stamp T.station n v d u) =
      Adjacent.born (fun j y => LocalFormal.runCoefficients R
        (Urban.buys R periodSystem S σ (finalStep T) 𝓐 y) T.order j (S.fire i))
        (T.stamp.menu.cloth (finalStep T).prev) 0 T.order k 0 := by
  rw [NativeRegulatorWilsonOpening.stopped T v d u hk, ← finalStep_next T]
  exact marked T v d u (finalStep T) 0 hk

end YM.Integration.NativeRegulatorActionStep
end
