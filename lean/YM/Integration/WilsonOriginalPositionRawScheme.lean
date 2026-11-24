import YM.Integration.WilsonPositionPhysicalCellTest
import YM.Integration.WilsonPositionRawEpoch
import YM.Integration.WilsonPositionDetectorMeshPrice
import YM.Integration.WilsonPositionGradedThermometerGround
import YM.Integration.WilsonOriginalPositionScheme

/-! Comparison of the enrolled original Wilson fields on their true compact test cells with the
independently filed finite lattice batch. The leading panel and first two scalar bills are automatic. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPositionRawScheme
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

/-- One shared compact physical source, its authentic convergent labels, and one independent
finite epoch at the reporting radius. Only degree three and higher can require a new scalar bill. -/
def compared (l : Ultrafilter (ℕ × ℕ)) (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (q : ℕ) : Prop :=
  ∃ (w : ℝ → (ℕ × ℕ) → Fin n → R.family.label d) (c : ℝ → Fin n → R.family.label d),
  (∀ᶠ r in trail, ∀ j, Tendsto (fun z=>w r z j) (l : Filter _) (𝓝 (c r j)) ∧
    S.project d (c r j) = WilsonPositionHomogeneousPanel.field F J Z d v r j) ∧
  ∀ δ>0, ∀ᶠ r in trail, ∃ i ≥ WilsonPositionAuxiliaryMesh.floor Z.run q (θ r),
    ∃ D : Handoff.Directory Z i (Handoff.Directory.budget G n d + q),
    (2<q → (1+WilsonPositionRawMesh.mass Z (Z.run.step i) q)^q*|θ r| ≤ δ) ∧
    ∀ᶠ z : ℕ × ℕ in (l : Filter _),
      ‖(∑ u : WilsonPositionPhysicalCellTest.Sites R z n,
          WilsonPositionPhysicalCellTest.mass φ r z u * R.family.ensemble (N:=z.1) (p:=z.2) (fun _=>d) u (w r z)) -
        ∑ k ∈ range (q+1), WilsonPositionRawEpoch.row Z D d φ v k *
          (WilsonPositionRawDetector.bare Z (Z.run.step i) q
            (WilsonPositionRawCutoff.thermometer Z F J A r z) : ℂ)^k‖ ≤ δ*|θ r|^q

include H in
theorem ground (ν : ℝ) (lead : Leading F J)
    (obedient : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d)
    (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) :
    WilsonPositionAuxiliaryMatch.booked Z F J d φ v 0 := by
  intro ε ep
  have view := WilsonPositionSeparatedProfileMatching.free Z T F J H lead obedient ν d φ v (half_pos ep)
  have finite0 : Tendsto (fun i=>finite Z (Z.run.step i) d φ v 0 0) atTop
      (𝓝 (coefficient Z T ν d φ v 0)) := by simpa [polynomial] using WilsonPositionFiniteMSBank.limit Z H ν d φ v 0 0
  obtain ⟨k,hk⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp finite0 (ε/2) (half_pos ep))
  filter_upwards [view] with r found
  let i := max k (WilsonPositionAuxiliaryMesh.floor Z.run 0 (θ r))
  refine ⟨i,le_max_right ..,?_⟩
  have h := hk i (le_max_left ..)
  have same : finite Z (Z.run.step i) d φ v 0 (θ r) = finite Z (Z.run.step i) d φ v 0 0 := by simp [finite]
  rw [same, pow_zero,mul_one]
  rw [dist_comm,dist_eq_norm] at h
  exact (norm_sub_le_norm_sub_add_norm_sub _ (coefficient Z T ν d φ v 0) _).trans
    ((add_le_add found h.le).trans_eq (add_halves ε))

include H in
theorem paid (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) {q : ℕ} (hq : 1 ≤ q)
    (lead : Leading F J) (book : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J)
    (prior : (l : Filter _) ≤ f.fuse) (coupled : Coupling G θ) (charged : compared F J Z A l d φ v q) :
    WilsonPositionAuxiliaryMatch.booked Z F J d φ v q := by
  obtain ⟨w,c,live,price⟩ := charged
  apply WilsonPositionMeasuredRawPanel.booked Z H d φ v q F J A hq lead book prior coupled
    (fun r => WilsonPositionHomogeneousPanel.panel d φ r (w r))
  · filter_upwards [live,RG17.positiveLength] with r labels hr
    exact WilsonPositionHomogeneousPanel.signed F J Z d φ v hG prior hr (w r) (c r)
      (fun j=>(labels j).1) (fun j=>(labels j).2)
  intro δ hd
  have small := coupled.conforms hG
  have legal := (goesFront (Expense.Stretched.runs Z.run)).eventually (Rose.usable Z.scheme Z.criterion hG)
  obtain ⟨i₀,h₀⟩ := eventually_atTop.mp legal
  have grows := (WilsonPositionAuxiliaryMesh.grows Z.run q trail coupled.positive small).eventually_ge_atTop i₀
  have low : ∀ᶠ r in trail, ∀ i ≥ WilsonPositionAuxiliaryMesh.floor Z.run q (θ r), q≤2 →
      (1+WilsonPositionRawMesh.mass Z (Z.run.step i) q)^q*|θ r| ≤ δ := by
    by_cases h : q≤2
    · exact (WilsonPositionDetectorMeshPrice.observed Z hG q h coupled.positive small hd).mono
        (fun _ ask i hi _=>ask i hi)
    · exact Eventually.of_forall fun _ _ _ hi=>(h hi).elim
  filter_upwards [price δ hd,grows,low] with r quote past known
  obtain ⟨i,hi,D,bill,signed⟩ := quote
  have use := h₀ i (past.trans hi)
  refine ⟨i,hi,if h : q≤2 then known i hi h else bill (by omega),?_⟩
  filter_upwards [signed] with z hz
  rw [WilsonPositionPhysicalCellTest.panel]
  unfold WilsonPositionMeasuredRawPanel.panel
  rw [←WilsonPositionRawPolynomial.issued Z _ q d φ v use,
    WilsonPositionRawEpoch.through Z H D d φ v q use le_rfl]
  exact hz

include H in
theorem original (ν : ℝ) {arch : Trace.Terrace.Arch R.family} (bliss : Bliss F l arch Y)
    (book : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J)
    (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0 < B) {C η : ℝ} (e : η < 1)
    (signed : WilsonPositionThermometerSevenFaceRate.charged (R:=R) hG (B:=B) l C η
      (WilsonPositionGradedThermometerHearing.offer F J Z.store Z.criterion A)
      (WilsonPositionOriginalTorusThermometer.actualRow (R:=R) Z.criterion hG (B:=B) Z.scheme))
    (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (lead : Leading F J)
    (obedient : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d) (X : Scaling S) (foundation : Foundation F reader)
    (charged : ∀ d n (φ : Test n) (v : Tags G d n) q, 0<q → compared F J Z A l d φ v q) :
    WilsonOriginalPositionScheme.Matched F J Z (T:=T) ν := by
  have heard := WilsonPositionGradedThermometerHearing.signed F J Z.store lead Z.criterion A book hG bliss.lies
  have physical := WilsonPositionOriginalTorusThermometer.original F P Z.criterion hG Z.scheme pace hB
    bliss e _ heard signed
  apply WilsonOriginalPositionScheme.graded F J Z H pace hB ν bliss A book e signed reader lead obedient X foundation
  intro d n φ v q
  rcases q with _ | k
  · exact ground F J Z H ν lead obedient d φ v
  · exact paid F J Z H A d φ v (by omega) lead book bliss.lies physical (charged d n φ v _ (by omega))

end YM.Integration.WilsonOriginalPositionRawScheme
