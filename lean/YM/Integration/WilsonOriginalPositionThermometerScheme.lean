import YM.Integration.WilsonOriginalPositionAuxiliaryScheme
import YM.Integration.WilsonMaxwellThermometerFirstRemainder

/-! The one measured position scheme from the genuine Wilson compact assay of the
corrected grade-six field and both corrected grade-four fields, on the same original cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPositionThermometerScheme
open Filter Function Finset Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb OPE OPE.Orbits
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.Fleet
open WilsonPositionSeparatedProfileMatching WilsonPositionFiniteMSBank WilsonPositionThermometerRunning
open scoped Topology BigOperators Classical
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    {hG : G.Simple} {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z hG T σ dial)
    {l : Ultrafilter (ℕ × ℕ)} {Y : (Bel R.family.book).Hierarchy}
    (A : ℝ → WilsonPositionThermometerCapStation.Group R.family 6)
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "P" => WilsonPositionPrescribedFrame.positioned F J Z.store

include H in
private theorem from_coordinate (ν : ℝ) {arch : Trace.Terrace.Arch R.family} (bliss : Bliss F l arch Y)
    (book : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J)
    (coupling : Coupling G θ)
    (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (lead : Leading F J)
    (obedient : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d) (X : Scaling S) (foundation : Foundation F reader)
    (charged : ∀ d n (φ : Test n) (v : Tags G d n) q, 0<q → WilsonOriginalPositionAuxiliaryScheme.signed_cells F J Z A l d φ v q) :
    WilsonOriginalPositionScheme.Matched F J Z (T:=T) ν := by
  apply WilsonOriginalPositionScheme.matched F J Z H ν reader lead obedient X foundation coupling
  intro d n φ v q
  rcases q with _ | k
  · exact WilsonOriginalPositionRawScheme.ground F J Z H ν lead obedient d φ v
  · apply WilsonOriginalPositionRawScheme.paid F J Z H A d φ v (by omega) lead book bliss.lies coupling
    exact WilsonOriginalPositionAuxiliaryScheme.compared F J Z H A d φ v _ coupling (charged d n φ v _ (by omega))

include H in
theorem original (ν : ℝ) {arch : Trace.Terrace.Arch R.family} (bliss : Bliss F l arch Y)
    (book : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J)
    (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0<B) {C η : ℝ} (slack : η<1)
    (thermometer : WilsonMaxwellThermometerFirstInvoice.invoice F J A Z.criterion Z.scheme hG B l C η)
    (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (lead : Leading F J)
    (obedient : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d) (X : Scaling S) (foundation : Foundation F reader)
    (charged : ∀ d n (φ : Test n) (v : Tags G d n) q, 0<q → WilsonOriginalPositionAuxiliaryScheme.signed_cells F J Z A l d φ v q) :
    WilsonOriginalPositionScheme.Matched F J Z (T:=T) ν := by
  apply from_coordinate F J Z H A ν bliss book _ reader lead obedient X foundation charged
  exact WilsonMaxwellThermometerFirstInvoice.original F J A Z.criterion Z.scheme hG B
    pace hB bliss book lead slack thermometer

include H in
theorem cutoff_first (ν : ℝ) {arch : Trace.Terrace.Arch R.family} (bliss : Bliss F l arch Y)
    (book : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J)
    (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0<B)
    (zero : ℝ→(ℕ×ℕ)→ℝ)
    (ground : ∀ᶠ r in trail,Tendsto (zero r) (l : Filter _) (𝓝
      (((Rose.test Z.criterion).applyTo (WilsonPositionGradedThermometerGround.ground
        (WilsonPositionCorrectedCap.adjusted F J Z.store A r))).re)))
    (thermometer : Tendsto (fun x : ℝ×(ℕ×ℕ) => WilsonMaxwellThermometerFirstRemainder.error F J A
      Z.criterion Z.scheme hG B zero x.1 x.2) (trail.curry (l : Filter _)) (𝓝 0))
    (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (lead : Leading F J)
    (obedient : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d) (X : Scaling S) (foundation : Foundation F reader)
    (charged : ∀ d n (φ : Test n) (v : Tags G d n) q, 0<q → WilsonOriginalPositionAuxiliaryScheme.signed_cells F J Z A l d φ v q) :
    WilsonOriginalPositionScheme.Matched F J Z (T:=T) ν := by
  apply from_coordinate F J Z H A ν bliss book _ reader lead obedient X foundation charged
  exact WilsonMaxwellThermometerFirstRemainder.original F J A Z.criterion Z.scheme hG B
    pace hB bliss book lead zero ground thermometer

end YM.Integration.WilsonOriginalPositionThermometerScheme
