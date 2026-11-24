import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedFullOrdinaryJet
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedDerivativeBook
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedDerivativeFrames
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedCartesianWords

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section
namespace YM.Integration.GradedFar.AppointedAllFieldCharts
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


theorem charts {n ℓ h : ℕ} {d : Fin n → ℕ} {K : Set (Points n)}
    (compact : IsCompact K) (sep : K ⊆ conf n)
    (received : ∀ hin, Window.Regained (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.last ((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).Post (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.P (Measure.outlook (_root_.IssuedMaxwell.ElectedPrescription.issued g hg).scheme (_root_.IssuedMaxwell.ElectedPrescription.issued g hg).criterion) ((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).T (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) n hin h)
    (hd : AppointedH140Through ℓ d) (q : ℕ) (ν : ℝ)
    
    :
    ∀ᶠ r in trail, ∀ o x, x ∈ K → ∀ v : AppointedH140Inputs g.core d,
      ∃ X : Set (Points n), IsOpen X ∧ x ∈ X ∧
        (∀ a : Toon g.core h, ContDiffOn ℝ ∞
          (fun y => coord a (actualField.{u} g hg periods mono r o v y)) X) ∧
        (∀ a : Toon g.core h, ContDiffOn ℝ ∞
          (fun y => coord a (actualCrop.{u} g hg periods mono q ν r v y)) X) := by
  let V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods mono)
  let N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let Q := WilsonGraphPaperPublication.perspective.{u} g hg
  let F := V.pupil.last
  let J := V.pupil.J
  let R := V.pupil.P
  let W := WilsonPositionPrescribedFrame.positioned F J N.store
  let Φ := WilsonPositionHomogeneousFrame.homogeneous F J N
  choose α hα using AppointedDerivativeFrames.future V Q
  filter_upwards [near_collar F R n h compact sep] with r ready
  intro o x hx v
  let X := {y : Points n | Window.arena F R h o r y} ∩ conf n
  refine ⟨X,(Window.season_open F R h o r n).inter (conf_open n),
    ⟨ready x hx o,sep hx⟩,?_,?_⟩
  · intro a y hy
    have actual := (Window.breeze F Φ R o r a y hy.1 v).contDiffWithinAt (s := X)
    simpa only [actualField, AppointedPaperOrdinary.packet g hg periods mono, Window.alarm] using actual
  · intro a
    have coefficient (k : ℕ) := AppointedDerivativeBook.lit F W Φ R N Q.MS Q.matching (AppointedDerivativeFrames.clock V Q) (AppointedDerivativeFrames.prepared V Q) a received α hα hd v k
    have series : ContDiffOn ℝ ∞ (fun y => ∑ k ∈ Finset.range (q+1),
        (V.T N r : ℂ)^k * coeff k (Window.Cargo (Measure.outlook N.scheme N.criterion) y v a)) (conf n) :=
      ContDiffOn.sum (fun k _ => contDiffOn_const.mul (coefficient k))
    apply (series.mono (show X ⊆ conf n from Set.inter_subset_right)).congr
    intro y _
    change coord a (msVector N (WilsonCapturedPhysicalMSDatum.original g.core) ν v y q h (V.T N r)) = _
    rw [← WilsonGraphPaperPublication.nominated.{u} g hg]
    rw [bookVector N Q.MS Q.matching ν, Window.cargo_crop N a, crop_eq]

end YM.Integration.GradedFar.AppointedAllFieldCharts
end

