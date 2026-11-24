import YM.Integration.WilsonGraphAppointedOrdinaryWordMass
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedAllFieldCharts
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedFullOrdinaryJet
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedDerivativeBook
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedDerivativeFrames
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedCartesianWords

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section
namespace YM.Integration.GradedFar.AppointedMeasuredJetMass
open Function Filter Set PowerSeries MeasureTheory Metric
open Wilson RG Source Extraction Table Spec PhysicalNext.Repeat.Legato RG17 FullVolume
open Climb Trace.Pilot PhysMS OPE OPE.Orbits
open XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open MS MS.Native MS.Land MS.Fleet
open Dframe O O.Score O.Enh FVA2.GradedFar
open Batch Auth Tariff Tariff.Playbill Tariff.Sunshine
open Answer.ContinuumLimit Answer.ContinuumLimit.Vision
open scoped Topology BigOperators Classical ContDiff

universe u
variable (g : YangMills.GaugeGroup) (hg : g.IsSimple)
variable (periods : ℕ → ℕ) (mono : StrictMono periods)




private abbrev submitted {n : ℕ} (d : Fin n → ℕ) (v : AppointedH140Inputs g.core d) :
    Fin n → Σ e : ℕ, (YangMills.maxwellReference g).sector e :=
  fun i => ⟨d i, v i⟩


private abbrev actualField {n h : ℕ} {d : Fin n → ℕ} (r : ℝ) (o : E4)
    (v : AppointedH140Inputs g.core d) (x : Points n) : Sec g.core h :=
  (_root_.YM.Answer.ContinuumLimit.AppointedOrdinaryPacket.measurement hg (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (_root_.YM.Integration.WilsonGraphPaperPublication.perspective.{u} g hg)).wilsonOPE
    r h (submitted g d v) o x
private abbrev actualCrop {n h : ℕ} {d : Fin n → ℕ} (q : ℕ) (ν r : ℝ)
    (v : AppointedH140Inputs g.core d) (x : Points n) : Sec g.core h :=
  msVector (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (_root_.YM.Integration.WilsonCapturedPhysicalMSDatum.original g.core)
    ν v x q h ((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).T (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) r)



open WilsonGraphUniformMixedShapeMass
theorem signedPrice {n h : ℕ} {d : Fin n → ℕ} {K : Set (Points n)}
    (compact : IsCompact K) (sep : K ⊆ conf n)
    (received : ∀ hin, Window.Regained (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.last ((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).Post (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.P (Measure.outlook (_root_.IssuedMaxwell.ElectedPrescription.issued g hg).scheme (_root_.IssuedMaxwell.ElectedPrescription.issued g hg).criterion) ((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).T (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) n hin h)
    (word : TraceOrder n) (q : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r in trail, ∀ (o : E4) (x : Points n), x ∈ K →
      ∀ (v : AppointedH140Inputs g.core d) (out : Module.Dual ℂ (Sec g.core h)),
      (∀ z, ‖out z‖ ≤ YangMills.Matching.sectorMass (B := YangMills.maxwellReference g) z) →
      ‖δ word (fun y => out (actualField.{u} g hg periods mono r o v y)) x -
        δ word (fun y => out (actualCrop.{u} g hg periods mono q (FVA2.Teller.logNu 1) r v y)) x‖ ≤
          A * inputMass g (d := d) v * |((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).T (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) r)|^(q+1) := by
  let V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods mono)
  let N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let Q := WilsonGraphPaperPublication.perspective.{u} g hg
  choose α hα using AppointedDerivativeFrames.future V Q
  let L := Finset.univ.sup d
  have hd : AppointedH140Through L d := fun i => Finset.le_sup (f := d) (Finset.mem_univ i)
  have paid := AppointedOrdinaryWordMass.onReader (g := g) (F := V.pupil.last)
    (J := V.Pre N) (P := V.Post N) (R := V.pupil.P) (Z := N) (M := Q.MS) (H := Q.matching)
    (ν := FVA2.Teller.logNu 1) (ht := AppointedDerivativeFrames.clock V Q)
    (Hp := AppointedDerivativeFrames.prepared V Q) (he := hd) (Hn := received) (α := α) (hα := hα)
    (hK := compact) (hx := sep) word q
  rw [WilsonGraphPaperPublication.nominated.{u} g hg] at paid
  simpa only [actualField, actualCrop, AppointedPaperOrdinary.packet g hg periods mono] using paid

theorem allOrders {n h : ℕ} {d : Fin n → ℕ} {K : Set (Points n)}
    (compact : IsCompact K) (sep : K ⊆ conf n)
    (received : ∀ hin, Window.Regained (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.last ((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).Post (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.P (Measure.outlook (_root_.IssuedMaxwell.ElectedPrescription.issued g hg).scheme (_root_.IssuedMaxwell.ElectedPrescription.issued g hg).criterion) ((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).T (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) n hin h)
    (q j : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r in trail, ∀ (o : E4) (x : Points n), x ∈ K →
      ∀ (v : AppointedH140Inputs g.core d) (out : Module.Dual ℂ (Sec g.core h)),
      (∀ z, ‖out z‖ ≤ YangMills.Matching.sectorMass (B := YangMills.maxwellReference g) z) →
      ∀ l : Fin (j+1),
      ‖iteratedFDeriv ℝ l.val (fun y => out (actualField.{u} g hg periods mono r o v y)) x -
        iteratedFDeriv ℝ l.val (fun y => out (actualCrop.{u} g hg periods mono q (FVA2.Teller.logNu 1) r v y)) x‖ ≤
          A * inputMass g (d := d) v * |((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).T (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) r)|^(q+1) := by
  let U := E4 × {x : Points n // x ∈ K} × AppointedH140Inputs g.core d ×
    {out : Module.Dual ℂ (Sec g.core h) // ∀ z, ‖out z‖ ≤
      YangMills.Matching.sectorMass (B := YangMills.maxwellReference g) z}
  let physical (r : ℝ) (u : U) (y : Points n) :=
    u.2.2.2.val (actualField.{u} g hg periods mono r u.1 u.2.2.1 y)
  let filed (r : ℝ) (u : U) (y : Points n) :=
    u.2.2.2.val (actualCrop.{u} g hg periods mono q (FVA2.Teller.logNu 1) r u.2.2.1 y)
  let jets (r : ℝ) (u : U) (l : Fin (j+1)) :=
    iteratedFDeriv ℝ l.val (physical r u) u.2.1.val - iteratedFDeriv ℝ l.val (filed r u) u.2.1.val
  let err (r : ℝ) (u : U) := inputMass g (d := d) u.2.2.1 * |((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).T (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) r)|^(q+1)
  let L := Finset.univ.sup d
  have hd : AppointedH140Through L d := fun i => Finset.le_sup (f := d) (Finset.mem_univ i)
  have smooth := AppointedAllFieldCharts.charts.{u} (h := h) g hg periods mono compact sep received hd q (FVA2.Teller.logNu 1)
  have one : ∀ (l : Fin (j+1)) (w : Fin l.val → Fin n × Axis),
      ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ r in trail, ∀ u : U,
        ‖jets r u l (fun i => WilsonGraphCartesianJetBound.axis (w i))‖ ≤ D * err r u := by
    intro l w
    obtain ⟨D,hD,paid⟩ := signedPrice.{u} (d := d) g hg periods mono compact sep received
      (AppointedCartesianWords.trace l.val w) q
    refine ⟨D,hD,?_⟩
    filter_upwards [smooth, paid] with r hr hp
    intro u
    obtain ⟨X,hX,inside,hf,hg'⟩ := hr u.1 u.2.1.val u.2.1.property u.2.2.1
    have h := hp u.1 u.2.1.val u.2.1.property u.2.2.1 u.2.2.2.val u.2.2.2.property
    have fSmooth : ContDiffOn ℝ ∞ (physical r u) X := AppointedFullOrdinaryJet.scalarSmooth u.2.2.2.val _ hf
    have gSmooth : ContDiffOn ℝ ∞ (filed r u) X := AppointedFullOrdinaryJet.scalarSmooth u.2.2.2.val _ hg'
    change ‖δ (AppointedCartesianWords.trace l.val w) (physical r u) u.2.1.val -
      δ (AppointedCartesianWords.trace l.val w) (filed r u) u.2.1.val‖ ≤ _ at h
    rw [AppointedCartesianWords.onWord hX fSmooth inside l.val w,
      AppointedCartesianWords.onWord hX gSmooth inside l.val w] at h
    simpa only [jets, err, mul_assoc, sub_apply] using h
  have positive (r : ℝ) (u : U) : 0 ≤ err r u :=
    mul_nonneg (Finset.prod_nonneg fun _ _ => YangMills.Matching.sectorMass_nonneg _) (pow_nonneg (abs_nonneg _) _)
  obtain ⟨A,hA,paid⟩ := WilsonGraphCartesianJetBound.uniform (I := fun _ : ℝ => U)
    trail j jets err positive one
  refine ⟨A,hA,?_⟩
  filter_upwards [paid] with r hr
  intro o x hx v out cap l
  simpa only [jets, physical, filed, err, mul_assoc] using hr (o, ⟨x,hx⟩, v, ⟨out,cap⟩) l

end YM.Integration.GradedFar.AppointedMeasuredJetMass
end

