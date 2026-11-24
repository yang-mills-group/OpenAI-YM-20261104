import YM.Integration.WilsonOriginalPositionCellBridge
import YM.Integration.WilsonPositionBareDetectorStability

/-! The actual independent compact program may use the measured coupling once at each
fixed real radius. The physical side retains its original ordered Wilson field readings. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPositionReportedCell
open Filter Function Finset Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb OPE OPE.Orbits
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open Next.UVStress Cells Push.GridApprox
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

/-- The same fully corrected original fields, tested at independently varying positions.
One elected auxiliary date, compact profile and measured scalar are fixed throughout one comparison. -/
def reported (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (q : ℕ) : Prop :=
  ∀ δ>0, ∃ (C : ℝ) (b : ℕ), ∀ᶠ r in trail, ∃ i ≥ WilsonPositionAuxiliaryMesh.floor Z.run q (θ r),
    ∃ D : Handoff.Directory Z i (Handoff.Directory.budget G n d + q), (i:ℝ) ≤ C*(-Real.log (θ r))^b ∧
      let u := WilsonPositionRawDetector.bare Z (Z.run.step i) q (θ r)
      ‖observed Z F J none d φ v r - WilsonPositionOriginalCellAverage.average (Z.run.step i) φ
        (WilsonPositionEpochCellTariff.data D d q v (u:ℂ))‖ ≤ δ*|θ r|^q

/-- An original finite price on the measured fields can be passed to the continuum in its
prescribed order at fixed radius, with the submitted auxiliary comparison held fixed. -/
theorem ordered (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) {r : ℝ} (hr : 0<r)
    (c : Fin n → R.family.label d)
    (filed : ∀ i, S.project d (c i) = WilsonPositionHomogeneousPanel.field F J Z d v r i)
    (a : ℂ) (E : ℝ) (priced : f.late (fun N p=>‖((R.family.S.a N : ℂ)^(4*n)*
      ∑ u : WilsonPositionPhysicalCellTest.Sites R (N,p) n, dilate hr φ (Extraction.Order.cells R.family N p u) *
        R.family.ensemble (N:=N) (p:=p) (fun _=>d) u c)-a‖ ≤ E)) :
    ‖observed Z F J none d φ v r-a‖ ≤ E := by
  obtain ⟨ready,lim,each,outer⟩ := WilsonPositionPhysicalCellTest.ordered φ F J Z d v hr c filed
  apply le_of_tendsto ((outer.sub_const a).norm)
  filter_upwards [ready,priced] with k good paid
  exact le_of_tendsto (((each (f.per k) good).sub_const a).norm) paid

include H in
theorem cells (lead : Leading F J) (book : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J)
    (prior : (l : Filter _) ≤ f.fuse) (coordinate : Coupling G θ)
    (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (q : ℕ) (hq : 0<q)
    (test : reported F J Z d φ v q) : WilsonOriginalPositionAuxiliaryScheme.signed_cells F J Z A l d φ v q := by
  let c (r : ℝ) (i : Fin n) := S.representative d (WilsonPositionHomogeneousPanel.field F J Z d v r i)
  refine ⟨fun r _=>c r,c,Eventually.of_forall (fun _ i=>⟨tendsto_const_nhds,S.rep ..⟩),?_⟩
  intro δ hδ
  obtain ⟨C,b,dates⟩ := test (δ/4) (by linarith)
  refine ⟨C,b,?_⟩
  have zero := coordinate.conforms hG
  have assay := WilsonPositionRawCutoff.measured Z F J lead A book hG prior
  have stable := WilsonPositionBareDetectorStability.measured Z q H hq trail coordinate.positive zero C b
  have sampled := WilsonPositionOriginalCellAverage.paid φ Z H q v trail coordinate.positive zero C b
    (show 0<δ/4 by linarith)
  have soft : ∀ᶠ r in trail, |θ r| < 1/4 := zero.abs.eventually_lt_const (by norm_num)
  filter_upwards [dates,assay,stable,sampled,soft,coordinate.positive,RG17.positiveLength]
    with r dated thaw continuity budget small hot pos
  obtain ⟨i,low,D,upper,price⟩ := dated
  refine ⟨i,low,D,fun _=>upper,?_⟩
  let m := Z.run.step i
  let u := WilsonPositionRawDetector.bare Z m q (θ r)
  have hu : |u| ≤ 1 := by
    dsimp only [u,WilsonPositionRawDetector.bare]
    split
    next h => exact (Classical.choose_spec h).1.trans (by linarith)
    next => simp
  have quadrature := budget i low upper D le_rfl u hu
  let bank := fun x : ℝ => ∑ k ∈ range (q+1),WilsonPositionRawEpoch.row Z D d φ v k*(x:ℂ)^k
  have hbank : Continuous bank := by dsimp [bank]; fun_prop
  have settled := hbank.continuousAt.tendsto.comp ((continuity i low upper).tendsto.comp thaw)
  have actual := WilsonPositionHomogeneousPanel.representatives F J Z d φ v hG prior pos
  have endprice : ‖observed Z F J none d φ v r-bank u‖ < δ*|θ r|^q := by
    let e := WilsonPositionOriginalCellAverage.average m φ (WilsonPositionEpochCellTariff.data D d q v (u:ℂ))
    have hnorm := norm_sub_le_norm_sub_add_norm_sub (observed Z F J none d φ v r) e (bank u)
    have hquad : ‖e-bank u‖ ≤ (δ/4)*(θ r)^(q+1) := by rw [norm_sub_rev]; exact quadrature
    have hpow : (θ r)^(q+1) ≤ |θ r|^q := by
      rw [abs_of_pos hot,pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hot.le _) (by rw [abs_of_pos hot] at small;linarith)
    have bill := (hquad.trans (mul_le_mul_of_nonneg_left hpow (by linarith)))
    have left : ‖observed Z F J none d φ v r-e‖≤(δ/4)*|θ r|^q := price
    have margin := mul_pos hδ (pow_pos (abs_pos.mpr hot.ne') q)
    linarith
  have along := (actual.sub settled).norm.eventually_lt_const endprice
  filter_upwards [along] with z hz
  rw [←WilsonPositionPhysicalCellTest.panel φ r z d (fun _=>c r)]
  exact hz.le

include H in
theorem original (ν : ℝ) {arch : Trace.Terrace.Arch R.family} (bliss : Bliss F l arch Y)
    (book : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J)
    (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0<B) {C η : ℝ} (slack : η<1)
    (thermometer : WilsonMaxwellThermometerFirstInvoice.invoice F J A Z.criterion Z.scheme hG B l C η)
    (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (lead : Leading F J)
    (obedient : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d) (X : Scaling S) (foundation : Foundation F reader)
    (charged : ∀ d n (φ : Test n) (v : Tags G d n) q, 0<q → reported F J Z d φ v q) :
    WilsonOriginalPositionScheme.Matched F J Z (T:=T) ν := by
  have coordinate := WilsonMaxwellThermometerFirstInvoice.original F J A Z.criterion Z.scheme hG B
    pace hB bliss book lead slack thermometer
  apply WilsonOriginalPositionThermometerScheme.original F J Z H A ν bliss book pace hB slack thermometer
    reader lead obedient X foundation
  exact fun d n φ v q hq=>cells F J Z H A lead book bliss.lies coordinate d φ v q hq (charged d n φ v q hq)

end YM.Integration.WilsonOriginalPositionReportedCell
