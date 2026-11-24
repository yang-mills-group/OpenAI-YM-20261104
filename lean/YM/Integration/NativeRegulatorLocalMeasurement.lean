import YM.Integration.NativeRegulatorActionStep

/-! The complete complex smeared finite regulator measurement in the
normalized local RG02 coefficients of the very same Run and marker. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.NativeRegulatorLocalMeasurement

open Function Filter Lattice Wilson Precision RG Labels PhysicalNext.Repeat.Legato
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Moving
open Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Prim Diagram Diagram.Formal
open PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth
open Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2
open Integral Exterior Arm Marker Multi Pipeline Pipeline.See Period.Field Sound
open NativeFormalSharedCoupling NativeFormalPrescriptionAgreement NativeFormalRegulatorCollector
open WilsonLimitConstruction.FundedFormalEconomy NativeFormalDiagonalCollector PowerSeries
open scoped Classical BigOperators Topology

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

open FormalOPE.RG10.Carryon

/-- The actual local normalized coefficient bank at the stopping edge,
re-expressed using its prescribed finite prior rating. -/
def exhibit : Perot.Exhibit 𝓑 T.station R.family.labels :=
  fun n v d u => mk fun k => if k ≤ T.order then
    let b := NativeRegulatorActionStep.finalStep T
    let V := T.stamp.traces T.station n σ v d u
    Adjacent.born (fun j y => LocalFormal.runCoefficients R (Urban.buys R periodSystem S σ b V y)
      T.order j (S.fire i)) (T.stamp.menu.cloth b.prev) 0 T.order k 0 else 0

theorem original : ProgramT.Ink (program R) Z R C (schedule Z C T.order) (above Z C T.order)
    T.calibrate T.order T.stop T.location S i T.stamp T.station = exhibit T := by
  funext n v d u
  apply PowerSeries.ext
  intro k
  rw [exhibit, coeff_mk]
  split_ifs with hk
  · exact NativeRegulatorActionStep.stopped T v d u hk
  change coeff k (mk (fun e => if e ≤ T.order then _ else (0:ℂ))) = _
  rw [coeff_mk, if_neg hk]

/-- The normalized measurement after the original spatial sum, real panel,
physical field normalization and coupling normalization. -/
def rack : Rack R.family.labels :=
  let a : Rack R.family.labels := fun d => YM.FVAAlt2.Home.Profiles.takeReal ∘
    Perot.Raw 𝓑 T.station (exhibit T) (Study.Plan R) d
  fun d => YM.FVAAlt2.Home.mix (mintRack (Row a (Study.Plan R).stock) d) (A d)

theorem rack_eq : ProgramT.Matter (program R) Z R C (schedule Z C T.order) (above Z C T.order)
    T.calibrate T.order T.stop T.location S i T.stamp A T.station = rack T := by
  unfold ProgramT.Matter ProgramT.sourceRead ProgramT.Alive ProgramT.skin rack
  rw [original T]

def measure (a : NativeFormalDiagonalCollector.Request R.family.labels) : ℂ :=
  NativeFormalComplexCollector.fields a.field fun v =>
    Complex.mk (coeff a.order (rack T a.horizon ⟨a.profile,v⟩))
      (coeff a.order (rack T a.horizon (NativeFormalComplexCollector.rotate ⟨a.profile,v⟩)))

theorem measure_eq (a : NativeFormalDiagonalCollector.Request R.family.labels) :
    T.measure a = measure T a := by
  unfold Trial.measure measure
  rw [rack_eq T]

variable {r : ℝ} (J : PositionX.Bend.Booth r (warehouse R).F)
  (X : FVA2.Pic.pass (warehouse R) hG W.data J)

/-- Every finite physical field and test demand is met by these normalized
local integral measurements on the actual family of diverging cutoffs. -/
theorem all_tests (H : AllTests W μ J X P Z C A) :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (i : I) (S : Marker.Census I) (g : G.ColorIndex),
    ∃ T : Demand R.family.labels → Trial W μ P Z C A g i S,
      (∀ z, z.2 + 1 ≤ (T z).order) ∧ Filter.Tendsto (fun z => (T z).cutoff) Filter.atTop Filter.atTop ∧
      ∀ a : NativeFormalDiagonalCollector.Request R.family.labels,
        Filter.Tendsto (fun z => measure (T z) a) Filter.atTop (𝓝 (target W μ J X a)) := by
  intro E _ _ e S g
  obtain ⟨T,hO,hC,hT⟩ := H E e S g
  exact ⟨T,hO,hC,fun a => (hT a).congr' (Filter.Eventually.of_forall fun z => measure_eq (T z) a)⟩

end YM.Integration.NativeRegulatorLocalMeasurement
end
