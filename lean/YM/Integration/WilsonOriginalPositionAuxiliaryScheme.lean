import YM.Integration.WilsonOriginalPositionRawScheme
import YM.Integration.WilsonPositionBareScalarDiagonal

/-! Original all-orders position scheme at a physical comparison with a common pre-regulator
auxiliary date. Its entire finite-order detector price is supplied by the original prescription. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPositionAuxiliaryScheme
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

/-- The same signed compact physical measurements compared at their common auxiliary date.
Its lower and upper cutoff bounds precede the original cutoff and period. -/
def signed_cells (l : Ultrafilter (ℕ × ℕ)) (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (q : ℕ) : Prop :=
  ∃ (w : ℝ → (ℕ × ℕ) → Fin n → R.family.label d) (c : ℝ → Fin n → R.family.label d),
  (∀ᶠ r in trail, ∀ j, Tendsto (fun z=>w r z j) (l : Filter _) (𝓝 (c r j)) ∧
    S.project d (c r j) = WilsonPositionHomogeneousPanel.field F J Z d v r j) ∧
  ∀ δ>0, ∃ (C : ℝ) (k : ℕ), ∀ᶠ r in trail, ∃ i ≥ WilsonPositionAuxiliaryMesh.floor Z.run q (θ r),
    ∃ D : Handoff.Directory Z i (Handoff.Directory.budget G n d + q),
    (2<q → (i:ℝ) ≤ C*(-Real.log (θ r))^k) ∧
    ∀ᶠ z : ℕ × ℕ in (l : Filter _),
      ‖(∑ u : WilsonPositionPhysicalCellTest.Sites R z n,
          WilsonPositionPhysicalCellTest.mass φ r z u * R.family.ensemble (N:=z.1) (p:=z.2) (fun _=>d) u (w r z)) -
        ∑ k ∈ range (q+1), WilsonPositionRawEpoch.row Z D d φ v k *
          (WilsonPositionRawDetector.bare Z (Z.run.step i) q
            (WilsonPositionRawCutoff.thermometer Z F J A r z) : ℂ)^k‖ ≤ δ*|θ r|^q

include H in
theorem compared (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (q : ℕ)
    (coordinate : Coupling G θ) (charged : signed_cells F J Z A l d φ v q) :
    WilsonOriginalPositionRawScheme.compared F J Z A l d φ v q := by
  obtain ⟨w,c,live,receipt⟩ := charged
  refine ⟨w,c,live,?_⟩
  intro δ hd
  obtain ⟨C,k,window⟩ := receipt δ hd
  have funded := WilsonPositionBareScalarDiagonal.paid Z H q k C trail coordinate.positive (coordinate.conforms hG) hd
  filter_upwards [window,funded] with r use bill
  obtain ⟨i,hi,D,short,price⟩ := use
  exact ⟨i,hi,D,fun high=>bill i hi (short high),price⟩

include H in
theorem original (ν : ℝ) {arch : Trace.Terrace.Arch R.family} (bliss : Bliss F l arch Y)
    (book : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J)
    (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0 < B) {C η : ℝ} (e : η < 1)
    (signed : WilsonPositionThermometerSevenFaceRate.charged (R:=R) hG (B:=B) l C η
      (WilsonPositionGradedThermometerHearing.offer F J Z.store Z.criterion A)
      (WilsonPositionOriginalTorusThermometer.actualRow (R:=R) Z.criterion hG (B:=B) Z.scheme))
    (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (lead : Leading F J)
    (obedient : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d) (X : Scaling S) (foundation : Foundation F reader)
    (charged : ∀ d n (φ : Test n) (v : Tags G d n) q, 0<q → signed_cells F J Z A l d φ v q) :
    WilsonOriginalPositionScheme.Matched F J Z (T:=T) ν := by
  have heard := WilsonPositionGradedThermometerHearing.signed F J Z.store lead Z.criterion A book hG bliss.lies
  have physical := WilsonPositionOriginalTorusThermometer.original F P Z.criterion hG Z.scheme pace hB
    bliss e _ heard signed
  apply WilsonOriginalPositionRawScheme.original F J Z H A ν bliss book pace hB e signed reader lead obedient X foundation
  intro d n φ v q hq
  exact compared F J Z H A d φ v q physical (charged d n φ v q hq)

end YM.Integration.WilsonOriginalPositionAuxiliaryScheme
