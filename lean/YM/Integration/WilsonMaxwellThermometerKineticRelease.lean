import YM.Integration.WilsonMaxwellThermometerKineticRequest

/-! The position dictionary from the joint target and seven-face comparison on one funded course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerKineticRelease
open Filter Set Function Maxwell XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Register FVA2.Scale MS MS.Fleet MS.Land Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits Climb PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionSeparatedProfileMatching
open scoped Topology Classical
variable {G : Gauge} (Z : WilsonPrescription G) {R : Run G} {f : Extraction.Order}
    {S : Table R.family.book} (F : Final R.family f S) (J : ℝ → tower S) (A : ℝ → Group R.family 6)
    {Y : Ultrafilter (ℕ×ℕ)} {H : (Bel R.family.book).Hierarchy} {arch : Trace.Terrace.Arch R.family}
    (simple : G.Simple) {B : ℕ} (hB : 0<B) (pace : WilsonWindowReportingPace.Slow R.kit) (fine index : ℝ→ℕ)
    (bliss : Bliss F Y arch H) (book : Book (f:=f) (l:=Y) (H:=H) A J) (lead : Leading F J)
local notation "visits" => trail.curry (Y : Filter (ℕ×ℕ))
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "m" => WilsonMeasuredWindow.stop R.family.path.levels simple B
local notation "u" => WilsonMaxwellThermometerKineticFineRose.axis (R:=R) fine
local notation "thermal" => WilsonPositionRawCutoff.thermometer Z F J A
local notation "enrolled" => WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=simple) (B:=B) Z fine index
local notation "earned" => WilsonMaxwellThermometerKineticRequest.earned (Y:=Y) Z F J A simple (B:=B) fine index
variable {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {σ : Prescription (Press.portDeck G)}
    {dial : Bool} (M : Main.Match Z simple T σ dial)

include hB pace bliss book lead in
theorem running (schedule : enrolled) (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n)
    (first : earned d φ v 1) :
    Tendsto (fun w:ℝ×(ℕ×ℕ)=>thermal w.1 w.2/u w) visits (𝓝 1) ∧
    Tendsto (fun r=>θ r/(Real.sqrt (arch.β (m r)))⁻¹) trail (𝓝 1) ∧ Coupling G θ := by
  obtain ⟨E,test⟩:=WilsonMaxwellThermometerKineticRequest.first Z F J A simple fine index d φ v first
  exact WilsonMaxwellThermometerKineticFineRose.original Z F J A simple hB fine index pace bliss book lead schedule E test

include hB pace bliss book lead M in
theorem original (schedule : enrolled) (ν : ℝ)
    (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (obedient : ∀ j,∀ᶠ r in trail, Frame.obedient F H (J r) j) (X : Scaling S) (foundation : Foundation F reader)
    (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (q : ℕ)
    (first : earned d φ v 1) (target : 0<q → earned d φ v q) :
    Coupling G θ ∧ matchesThrough Z T F J ν d φ v q := by
  have rate := (running Z F J A simple hB pace fine index bliss book lead schedule d φ v first).2.2
  refine ⟨rate,WilsonPositionAuxiliaryMatch.measured Z M F J ν d φ v q reader lead obedient X foundation rate ?_⟩
  cases q with
  | zero => exact WilsonOriginalPositionRawScheme.ground F J Z M ν lead obedient d φ v
  | succ k =>
    have qpos:0<k+1:=by omega
    exact WilsonOriginalPositionFineScheme.observed F J Z M A hB pace fine index schedule lead book bliss.lies rate
      d φ v _ qpos (WilsonMaxwellThermometerKineticRequest.restored Z F J A simple hB fine index d φ v pace
        schedule bliss.lies rate _ (target qpos))

include hB pace bliss book lead M in
theorem matched (schedule : enrolled) (ν : ℝ)
    (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (obedient : ∀ j,∀ᶠ r in trail, Frame.obedient F H (J r) j) (X : Scaling S) (foundation : Foundation F reader)
    (sold : ∀ d n (φ : Test n) (v : Tags G d n) q, 0<q → earned d φ v q) :
    WilsonOriginalPositionScheme.Matched F J Z (T:=T) ν := by
  have rate := (running Z F J A simple hB pace fine index bliss book lead schedule 6
    (Rose.test Z.criterion) (Rose.tag G) (sold 6 3 (Rose.test Z.criterion) (Rose.tag G) 1 (by decide))).2.2
  apply WilsonOriginalPositionScheme.matched F J Z M ν reader lead obedient X foundation rate
  intro d n φ v q
  cases q with
  | zero => exact WilsonOriginalPositionRawScheme.ground F J Z M ν lead obedient d φ v
  | succ k =>
    have qpos : 0<k+1:=by omega
    exact WilsonOriginalPositionFineScheme.observed F J Z M A hB pace fine index schedule lead book bliss.lies rate
      d φ v _ qpos (WilsonMaxwellThermometerKineticRequest.restored Z F J A simple hB fine index d φ v pace
        schedule bliss.lies rate _ (sold d n φ v _ qpos))

end YM.Integration.WilsonMaxwellThermometerKineticRelease
