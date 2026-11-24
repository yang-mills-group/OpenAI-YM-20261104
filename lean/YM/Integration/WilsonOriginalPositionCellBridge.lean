import YM.Integration.WilsonOriginalPositionThermometerScheme
import YM.Integration.WilsonPositionOriginalCellAverage

/-! Compare the physical Wilson panel and the prescribed position calculation on the same
continuous test with independently placed children, before using the single original scheme. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPositionCellBridge
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

/-- At a reporting radius, one common auxiliary date serves the complete signed evaluation.
The actual cutoff thermometer, all its legs, and every physical source share the same cutoff. -/
def submitted (l : Ultrafilter (ℕ × ℕ)) (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (q : ℕ) : Prop :=
  ∃ (w : ℝ → (ℕ × ℕ) → Fin n → R.family.label d) (c : ℝ → Fin n → R.family.label d),
  (∀ᶠ r in trail, ∀ j, Tendsto (fun z=>w r z j) (l : Filter _) (𝓝 (c r j)) ∧
    S.project d (c r j) = WilsonPositionHomogeneousPanel.field F J Z d v r j) ∧
  ∀ δ>0, ∃ (C : ℝ) (b : ℕ), ∀ᶠ r in trail, ∃ i ≥ WilsonPositionAuxiliaryMesh.floor Z.run q (θ r),
    ∃ D : Handoff.Directory Z i (Handoff.Directory.budget G n d + q), (i:ℝ) ≤ C*(-Real.log (θ r))^b ∧
    ∀ᶠ z : ℕ × ℕ in (l : Filter _),
      let u := WilsonPositionRawDetector.bare Z (Z.run.step i) q (WilsonPositionRawCutoff.thermometer Z F J A r z)
      ‖WilsonPositionHomogeneousPanel.panel d φ r (w r) z - WilsonPositionOriginalCellAverage.average
        (Z.run.step i) φ (WilsonPositionEpochCellTariff.data D d q v (u:ℂ))‖ ≤ δ*|θ r|^q

private theorem bare_bound (m : Mesh) (q : ℕ) (t : ℝ) : |WilsonPositionRawDetector.bare Z m q t| ≤ 4*|t| := by
  unfold WilsonPositionRawDetector.bare
  split
  next h => exact (Classical.choose_spec h).1
  next => simp

include H in
theorem cells (lead : Leading F J) (book : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J)
    (prior : (l : Filter _) ≤ f.fuse) (coordinate : Coupling G θ)
    (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (q : ℕ) (test : submitted F J Z A l d φ v q) :
    WilsonOriginalPositionAuxiliaryScheme.signed_cells F J Z A l d φ v q := by
  obtain ⟨w,c,projects,fees⟩ := test
  refine ⟨w,c,projects,?_⟩
  intro δ hδ
  obtain ⟨C,b,dates⟩ := fees (δ/2) (half_pos hδ)
  refine ⟨C,b,?_⟩
  have zero := coordinate.conforms hG
  have sampled := WilsonPositionOriginalCellAverage.paid φ Z H q v trail coordinate.positive zero C b (half_pos hδ)
  have read := WilsonPositionRawCutoff.measured Z F J lead A book hG prior
  have small : ∀ᶠ r in trail, |θ r| < 1/8 := zero.abs.eventually_lt_const (by norm_num)
  filter_upwards [dates,sampled,read,small,coordinate.positive] with r date price assay light pos
  obtain ⟨i,low,D,upper,hears⟩ := date
  refine ⟨i,low,D,fun _=>upper,?_⟩
  have free := assay.abs.eventually_lt_const (show |θ r| < 1/4 by linarith)
  filter_upwards [hears,free] with z seen bound
  let u := WilsonPositionRawDetector.bare Z (Z.run.step i) q (WilsonPositionRawCutoff.thermometer Z F J A r z)
  have hu : |u| ≤ 1 := (bare_bound Z _ _ _).trans (by linarith)
  have paid := price i low upper D le_rfl u hu
  let e := WilsonPositionOriginalCellAverage.average (Z.run.step i) φ (WilsonPositionEpochCellTariff.data D d q v (u:ℂ))
  rw [← WilsonPositionPhysicalCellTest.panel]
  refine (norm_sub_le_norm_sub_add_norm_sub _ e _).trans ?_
  rw [norm_sub_rev e]
  have hpow : (θ r)^(q+1) ≤ |θ r|^q := by
    rw [abs_of_pos pos,pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg pos.le _) (by rw [abs_of_pos pos] at light;linarith)
  exact (add_le_add seen (paid.trans (mul_le_mul_of_nonneg_left hpow (half_pos hδ).le))).trans (by ring_nf; rfl)

include H in
theorem original (ν : ℝ) {arch : Trace.Terrace.Arch R.family} (bliss : Bliss F l arch Y)
    (book : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J)
    (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0<B) {C η : ℝ} (slack : η<1)
    (thermometer : WilsonMaxwellThermometerFirstInvoice.invoice F J A Z.criterion Z.scheme hG B l C η)
    (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (lead : Leading F J)
    (obedient : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d) (X : Scaling S) (foundation : Foundation F reader)
    (charged : ∀ d n (φ : Test n) (v : Tags G d n) q, 0<q → submitted F J Z A l d φ v q) :
    WilsonOriginalPositionScheme.Matched F J Z (T:=T) ν := by
  have coordinate := WilsonMaxwellThermometerFirstInvoice.original F J A Z.criterion Z.scheme hG B
    pace hB bliss book lead slack thermometer
  apply WilsonOriginalPositionThermometerScheme.original F J Z H A ν bliss book pace hB slack
    thermometer reader lead obedient X foundation
  exact fun d n φ v q hq=>cells F J Z H A lead book bliss.lies coordinate d φ v q (charged d n φ v q hq)

end YM.Integration.WilsonOriginalPositionCellBridge
