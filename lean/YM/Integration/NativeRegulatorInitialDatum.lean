import YM.Integration.NativeRegulatorWilsonOpening

/-! The actual first local datum in the selected marked regulator trajectory,
with both native levels and literal transported Wilson input colors. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.NativeRegulatorInitialDatum

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
local notation:max "opening" j:max => Page.opening (𝓑).entire j
/-- The first physical step of the selected regulator path at station j. -/
def first (j : ℕ) : Flap (𝓑).entire :=
  ⟨j,0,by
    have h : 0 < (𝓑).long j := Nat.mul_pos ((𝓑).life _) ((𝓑).life _)
    change 0 < 2 * (𝓑).long j
    omega⟩

theorem before (j : ℕ) : (first T j).prev = opening j := rfl

/-- The level of its actual output. The physical input is at its successor. -/
def level (j : ℕ) : ℕ := (periodSystem).vol (first T j).next

variable (j : ℕ) (x : fieldDir G (R.family.side (level T j) (T.stop T.station)) 1)

include v

def datum : LocalFormal.Datum R.family S := Urban.buys R periodSystem S σ (first T j) 𝓐 x

theorem cutoff : (datum T v d u j x).cutoff = (datum T v d u j x).level + 1 :=
  (periodSystem).links (first T j)

theorem period : (datum T v d u j x).period = T.stop T.station := rfl

theorem output : (datum T v d u j x).level = level T j := rfl

omit v in
private theorem carry {V : Type} [DecidableEq V] (S : Marker.Census V) (i : V) (Γ : History G)
    (p m : ℕ) (s : Boot.Scout (G := G) m) {a b : ℕ} (h : a = b) :
    See.castF (X := fun n => Colors S G (Γ.S.side n p)) h (Boot.ink S i Γ a p s) = Boot.ink S i Γ b p s := by
  subst b
  rfl

/-- The previous-page colors transported to the input side are exactly
the true Wilson opening with the original inserted test. -/
theorem colors : (datum T v d u j x).colors = Boot.ink S i R.family.path
    ((datum T v d u j x).level+1) (datum T v d u j x).period (𝓕 j) := by
  change See.castF (X := fun a => Colors S G (R.family.path.S.side a σ))
    ((periodSystem).links (first T j)) (𝓐 (opening j)) = _
  rw [NativeRegulatorWilsonOpening.initial T v d u j]
  exact carry S i R.family.path σ _ (𝓕 j) ((periodSystem).links (first T j))

/-- Its path, marker, and spatial field all use that same funded cutoff,
including the full vacuum numerator/denominator. -/
theorem normalized :
    let D := datum T v d u j x
    D.denominator (RunFormalChain.fromRun R) T.order * D.ordinary (RunFormalChain.fromRun R) T.order =
      D.raw (RunFormalChain.fromRun R) T.order ∧
      Order.denominator (D.ordinary (RunFormalChain.fromRun R) T.order) = 1 ∧
      Order.denominator (D.markedLog (RunFormalChain.fromRun R) T.order) = 0 :=
  LocalFormal.run_normalization R (datum T v d u j x) T.order

end YM.Integration.NativeRegulatorInitialDatum
end
