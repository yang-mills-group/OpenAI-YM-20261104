import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedMeasuredJetMass
import YM.Integration.WilsonGraphMSVectorIssuedOrdinaryCrop

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace YM.Integration.GradedFar.AppointedPublicOrdinaryJets

open Function Filter Set PowerSeries MeasureTheory Metric
open Wilson RG Source Extraction Table Spec PhysicalNext.Repeat.Legato RG17 FullVolume
open Climb Trace.Pilot PhysMS OPE OPE.Orbits
open XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open MS MS.Native MS.Land MS.Fleet
open Dframe O O.Score O.Enh FVA2.GradedFar
open Batch Auth Tariff Tariff.Playbill Tariff.Sunshine
open Answer.ContinuumLimit Answer.ContinuumLimit.Vision
open scoped BigOperators Classical Topology ContDiff

universe u
variable (g : YangMills.GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (mono : StrictMono periods)
private abbrev V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods mono)
private abbrev N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Qstar := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev H := AppointedOrdinaryPacket.measurement hg (V.{u} g hg periods mono) (N g hg) (Qstar.{u} g hg)
private abbrev S := AppointedGraphOrdinaryConversion.filedConversion g hg

/-- The original raised-grade reader incomes at this arity and output grade on the published selection. -/
abbrev Receives (n h : ℕ) : Prop :=
  ∀ hin, Window.Regained (V.{u} g hg periods mono).pupil.last
    ((V.{u} g hg periods mono).Post (N g hg)) (V.{u} g hg periods mono).pupil.P
    (Measure.outlook (N g hg).scheme (N g hg).criterion) ((V.{u} g hg periods mono).T (N g hg)) n hin h

/-- Compare every derivative through the requested order on the issued graph model with the public mass price. -/
theorem onReader {n h : ℕ} (q j : ℕ) (d : Fin n → ℕ) (K : Set (YM.Points n))
    (compact : IsCompact K) (separated : K ⊆ conf n)
    (received : Receives.{u} g hg periods mono n h) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ (v : (i : Fin n) → (YangMills.maxwellReference g).sector (d i))
        (o : YangMills.Spacetime) (x : YM.Points n), x ∈ K →
      ∀ out : (YangMills.maxwellReference g).sector h →ₗ[ℂ] ℂ,
        (∀ w, ‖out w‖ ≤ YangMills.Matching.sectorMass (B := YangMills.maxwellReference g) w) →
      let a : Fin n → YangMills.Matching.Label (YangMills.maxwellReference g) := fun i => ⟨d i,v i⟩
      let t := (H.{u} g hg periods mono).clock r
      YangMills.Matching.shapeJetEstimateAt j
        (fun y => out ((H.{u} g hg periods mono).wilsonOPE r h a o y))
        (fun y => out (∑ k : Fin (q+1), (t : ℂ)^k.val • (S g hg).ope
          (_root_.IssuedMaxwell.GraphCoefficients.issued g) h k.val a y))
        x (A * (∏ i, YangMills.Matching.sectorMass (B := YangMills.maxwellReference g) (v i)) * |t|^(q+1)) := by
  obtain ⟨A,hA,cost⟩ := AppointedMeasuredJetMass.allOrders.{u} (h := h) (d := d)
    g hg periods mono compact separated received q j
  let L := Finset.univ.sup d
  have through : AppointedH140Through L d := fun i => Finset.le_sup (f := d) (Finset.mem_univ i)
  have charts := AppointedAllFieldCharts.charts.{u} (h := h) g hg periods mono compact separated
    received through q (Teller.logNu 1)
  refine ⟨A,hA,?_⟩
  filter_upwards [cost,charts] with r priced smooth
  intro v o x hx out contractive
  let a : AppointedH140Inputs g.core d := v
  let b : Sec g.core h →ₗ[ℂ] ℂ := out
  let t := (V.{u} g hg periods mono).T (N g hg) r
  let real : YM.Points n → ℂ := fun y =>
    b ((H.{u} g hg periods mono).wilsonOPE r h (fun i => ⟨d i, a i⟩) o y)
  let predicted : YM.Points n → ℂ := fun y =>
    b (msVector (N g hg) (WilsonCapturedPhysicalMSDatum.original g.core) (Teller.logNu 1) a y q h t)
  obtain ⟨X,hX,inside,actualCoords,formalCoords⟩ := smooth o x hx a
  have actualSmooth : ContDiffOn ℝ ∞ real X := AppointedFullOrdinaryJet.scalarSmooth b _ actualCoords
  have formalSmooth : ContDiffOn ℝ ∞ predicted X := AppointedFullOrdinaryJet.scalarSmooth b _ formalCoords
  have actualAt (k : ℕ) : ContDiffAt ℝ k real x :=
    (actualSmooth.contDiffAt (hX.mem_nhds inside)).of_le (WithTop.coe_le_coe.mpr le_top)
  have formalAt (k : ℕ) : ContDiffAt ℝ k predicted x :=
    (formalSmooth.contDiffAt (hX.mem_nhds inside)).of_le (WithTop.coe_le_coe.mpr le_top)
  apply (AppointedGraphMSVector.shapes g hg d a h q j t real b x _).mp
  refine ⟨actualAt j,formalAt j,?_⟩
  intro l hl
  change ‖iteratedFDeriv ℝ l (real - predicted) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply (actualAt l) (formalAt l)]
  exact priced o x hx a b contractive ⟨l,Nat.lt_succ_of_le hl⟩

end YM.Integration.GradedFar.AppointedPublicOrdinaryJets
end

