import YM.Integration.WilsonPositionOriginalTorusThermometer
import YM.Integration.WilsonOriginalPositionSchemeUniqueness
import YM.Integration.WilsonPositionAuxiliaryMatch
import YM.Integration.WilsonPositionThermometerStationReading
import YM.Integration.WilsonPositionOriginalOrientedFrame
import YM.Integration.WilsonPositionGradedThermometerHearing

/-! The original positioned thermometer and its homogeneous fields use one
MS prescription at all orders. The two physical input prices refer to this
same Wilson extraction. -/
set_option autoImplicit false
set_option format.width 180
noncomputable section
namespace YM.Integration.WilsonOriginalPositionScheme

open Filter Function Finset Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb OPE OPE.Orbits
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open WilsonPositionThermometerOrientedStation
open FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.Fleet
open scoped Topology BigOperators Classical

variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    {hG : G.Simple} {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z hG T σ dial)
local notation "P" => WilsonPositionPrescribedFrame.positioned F J Z.store
local notation "D" => WilsonPositionHomogeneousFrame.homogeneous F J Z
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z

include H in
/-- Use the unselected reading of the enrolled smooth profile. The smeared
coefficients are those of the common independently issued position bank. -/
theorem received (ν : ℝ)
    (profiles : ∀ d n (φ : Test n) (v : Fin n → Sec G d) q,
      WilsonPositionSeparatedProfileMatching.matchesThrough Z T F J ν d φ v q) :
    WilsonOriginalPositionSchemeUniqueness.heard F D θ (Measure.outlook Z.scheme Z.criterion) := by
  intro d n φ v k ε ep
  have entry (j : ℕ) : WilsonPositionSeparatedProfileMatching.coefficient Z T ν d φ v j =
      φ.applyTo (fun x => Jury.fxt (Measure.outlook Z.scheme Z.criterion d) x j v) := by
    rw [WilsonPositionSeparatedProfileMatching.filed Z T H ν]
    apply φ.apply_eq
    intro x hx
    simp only [WilsonPositionSeparatedProfileMatching.extended, Jury.fxt, dif_pos hx]
  filter_upwards [profiles d n φ v k ε ep] with r allviewers
  simpa only [WilsonPositionSeparatedProfileMatching.observed,
    WilsonPositionPhaseProfileTest.reading, WilsonPositionSeparatedProfileMatching.polynomial, entry]
    using allviewers none

def Matched (ν : ℝ) : Prop :=
    Coupling G θ ∧
    (∀ d n (φ : Test n) (v : Fin n → Sec G d) q,
      WilsonPositionSeparatedProfileMatching.matchesThrough Z T F J ν d φ v q) ∧
    (∃! pair : PowerSeries ℂ × Frames G, Tangent pair.1 ∧
      (∀ d, Base (pair.2 d)) ∧ WilsonOriginalPositionSchemeUniqueness.heard F D θ (fun d =>
        Facets.actMark (pair.2 d) (Facets.couple pair.1 (Equator.wave ν T d)))) ∧
    (∀ i j (h : i ≤ j), Walk h (Measure.Z Z.scheme Z.criterion ν T i)
      (Measure.Z Z.scheme Z.criterion ν T j)) ∧ O.Canon.Supplied Z T ν

include H in
theorem matched (ν : ℝ) {Y : (Bel R.family.book).Hierarchy}
    (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (lead : Leading F J)
    (paid : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d) (X : Scaling S) (foundation : Foundation F reader)
    (physical : Coupling G θ)
    (finite : ∀ d n (φ : Test n) (v : Fin n → Sec G d) q,
      WilsonPositionAuxiliaryMatch.booked Z F J d φ v q) : Matched F J Z (T:=T) ν := by
  have profiles (d n : ℕ) (φ : Test n) (v : Fin n → Sec G d) (q : ℕ) :=
    WilsonPositionAuxiliaryMatch.measured Z H F J ν d φ v q reader lead paid X foundation physical
      (finite d n φ v q)
  exact ⟨physical, profiles, WilsonOriginalPositionSchemeUniqueness.original F D Z H P ν physical
    (received F J Z H ν profiles)⟩

variable (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0 < B)

include H pace hB in
/-- The cutoff source is the true signed three-field numerator, including
any cutoff-dependent lifts. All other measurements use the physical
homogeneous frame attached to that same positioned thermometer. -/
theorem original (ν : ℝ) {l : Ultrafilter (ℕ × ℕ)} {arch : Trace.Terrace.Arch R.family}
    {Y : (Bel R.family.book).Hierarchy} (bliss : Bliss F l arch Y)
    {I : Type} [Fintype I] (basis : Module.Basis I ℂ ((Bel R.family.book).Field 6))
    (A : ℝ → Filing R.family 6 I)
    (basisFiled : ∀ m : ℕ, ∀ᶠ r in trail, Filed (f:=f) (Y:=l) Y basis r (J r) m (A r))
    {C η : ℝ} (e : η < 1)
    (signed : WilsonPositionThermometerSevenFaceRate.charged (R := R) hG (B := B) l C η
      (fun r z => (Rose.test Z.criterion).applyTo (WilsonPositionThermometerStationReading.full r
        (WilsonPositionOriginalOrientedFrame.lamps F J Z.store basis A r) z))
      (WilsonPositionOriginalTorusThermometer.actualRow (R:=R) Z.criterion hG (B:=B) Z.scheme))
    (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (lead : Leading F J)
    (paid : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d) (X : Scaling S) (foundation : Foundation F reader)
    (finite : ∀ d n (φ : Test n) (v : Fin n → Sec G d) q,
      WilsonPositionAuxiliaryMatch.booked Z F J d φ v q) : Matched F J Z (T:=T) ν := by
  let stars := WilsonPositionOriginalOrientedFrame.lamps F J Z.store basis A
  let offer (r : ℝ) (z : ℕ × ℕ) :=
    (Rose.test Z.criterion).applyTo (WilsonPositionThermometerStationReading.full r (stars r) z)
  have placed := WilsonPositionOriginalOrientedFrame.positioned F J Z.store basis A basisFiled lead bliss.lies 0
  have limit : ∀ᶠ r in trail, Tendsto (offer r) (l : Filter (ℕ × ℕ))
      (𝓝 (WilsonPositionThermometerReading.tested F P Z.criterion r)) := by
    filter_upwards [placed, RG17.positiveLength] with r hr positive
    exact WilsonPositionThermometerStationReading.signed F P r (stars r) hG bliss.lies hr Z.criterion positive
  have physical := WilsonPositionOriginalTorusThermometer.original F P Z.criterion hG Z.scheme pace hB
    bliss e offer limit signed
  exact matched F J Z H ν reader lead paid X foundation physical finite

include H pace hB in
theorem graded (ν : ℝ) {l : Ultrafilter (ℕ × ℕ)} {arch : Trace.Terrace.Arch R.family}
    {Y : (Bel R.family.book).Hierarchy} (bliss : Bliss F l arch Y)
    (A : ℝ → WilsonPositionThermometerCapStation.Group R.family 6)
    (book : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J)
    {C η : ℝ} (e : η < 1)
    (signed : WilsonPositionThermometerSevenFaceRate.charged (R:=R) hG (B:=B) l C η
      (WilsonPositionGradedThermometerHearing.offer F J Z.store Z.criterion A)
      (WilsonPositionOriginalTorusThermometer.actualRow (R:=R) Z.criterion hG (B:=B) Z.scheme))
    (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (lead : Leading F J)
    (paid : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d) (X : Scaling S) (foundation : Foundation F reader)
    (finite : ∀ d n (φ : Test n) (v : Fin n → Sec G d) q,
      WilsonPositionAuxiliaryMatch.booked Z F J d φ v q) : Matched F J Z (T:=T) ν := by
  have limit := WilsonPositionGradedThermometerHearing.signed F J Z.store lead Z.criterion A book hG bliss.lies
  have physical := WilsonPositionOriginalTorusThermometer.original F P Z.criterion hG Z.scheme pace hB
    bliss e _ limit signed
  exact matched F J Z H ν reader lead paid X foundation physical finite

end YM.Integration.WilsonOriginalPositionScheme
