import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedMeasuredJetPurchases
import YM.Integration.WilsonGraphAppointedPublicOrdinaryJets

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace YM.Integration.GradedFar.AppointedOrdinaryPurchases

open Function Filter Set PowerSeries MeasureTheory Metric
open Wilson RG Source Extraction Table Spec PhysicalNext.Repeat.Legato RG17 FullVolume
open Climb Trace.Pilot PhysMS OPE OPE.Orbits
open XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open MS MS.Native MS.Land MS.Fleet
open Dframe O O.Score O.Enh FVA2.GradedFar
open Batch Auth Tariff Tariff.Playbill Tariff.Sunshine
open Answer.ContinuumLimit Answer.ContinuumLimit.Vision
open scoped BigOperators Classical Topology ContDiff

universe u v
variable (g : YangMills.GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (mono : StrictMono periods)
private abbrev V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods mono)
private abbrev N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Qstar := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev H := AppointedOrdinaryPacket.measurement hg (V.{u} g hg periods mono) (N g hg) (Qstar.{u} g hg)
private abbrev S := AppointedGraphOrdinaryConversion.filedConversion g hg

/-- The public ordinary estimate on the selected physical hierarchy at one arity and output grade. -/
abbrev AtOutput (n h : ℕ) : Prop :=
  ∀ (q j : ℕ) (d : Fin n → ℕ) (K : Set (YM.Points n)), IsCompact K → K ⊆ conf n →
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
        x (A * (∏ i, YangMills.Matching.sectorMass (B := YangMills.maxwellReference g) (v i)) * |t|^(q+1))

/-- The original growing numerator fares at the raised input grades and the appointed output. -/
abbrev RaisedIncome (n h : ℕ) :=
  ∀ (hin : ℕ) {e : Fin n → ℕ}, AppointedH140Through hin e → ∀ {L : Set (YM.Points n)},
    IsCompact L → L ⊆ conf n → ∀ p : ℕ, 1 ≤ p → ∀ B : ℝ, 0 < B →
      YM.FVA2.GradedFar.AppointedTwoFiledPublicRows.UnselectedIncome.{u,v} g hg periods mono e h p L B

theorem fromRegained (n h : ℕ) (received : AppointedPublicOrdinaryJets.Receives.{u} g hg periods mono n h) :
    AtOutput.{u} g hg periods mono n h :=
  fun q j d K compact separated =>
    AppointedPublicOrdinaryJets.onReader.{u} g hg periods mono q j d K compact separated received

/-- The real one-input OPE has a public price at every output grade and every shape order. -/
theorem oneNear (h : ℕ) : AtOutput.{u} g hg periods mono 1 h :=
  fromRegained.{u} g hg periods mono 1 h
    (fun hin => YM.FVA2.GradedFar.AppointedOneNearPublic.regained.{u} g hg periods mono hin h)

/-- The many-input price consumes the signed numerator family at its actual raised grades. -/
theorem fromIncomes {n h : ℕ} (positive : 0 < n) (incomes : RaisedIncome.{u,v} g hg periods mono n h) :
    AtOutput.{u} g hg periods mono n h :=
  fromRegained.{u} g hg periods mono n h
    (fun hin => AppointedRaisedReceives.onIncomes.{u,v} g hg periods mono positive hin h (incomes hin))

end YM.Integration.GradedFar.AppointedOrdinaryPurchases
end

