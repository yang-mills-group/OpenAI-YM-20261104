import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedRaisedNumeratorCoordinates
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedRaisedReaderBook

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section
namespace YM.Integration.GradedFar.AppointedRaisedReceives
open Function Filter Set PowerSeries MeasureTheory Metric
open Wilson RG Source Extraction Table Spec PhysicalNext.Repeat.Legato RG17 FullVolume
open Climb Trace.Pilot PhysMS OPE OPE.Orbits
open XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open MS MS.Native MS.Land MS.Fleet
open Dframe O O.Score O.Enh FVA2.GradedFar
open Batch Auth Tariff Tariff.Playbill Tariff.Sunshine
open Answer.ContinuumLimit Answer.ContinuumLimit.Vision
open scoped Topology BigOperators Classical


universe u v
variable (g : YangMills.GaugeGroup) (hg : g.IsSimple)
variable (periods : ℕ → ℕ) (mono : StrictMono periods)
private abbrev V := _root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg
  (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)
private abbrev Q := _root_.YM.Integration.WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev W := _root_.YM.Answer.ContinuumLimit.AppointedOrdinaryPacket.measurement hg
  (V.{u} g hg periods mono) (N g hg) (Q.{u} g hg)


theorem onIncomes {n : ℕ} (hn : 0 < n) (hin hout : ℕ)
    (incomes : ∀ {e : Fin n → ℕ}, Through hin e → ∀ {K : Set (Points n)},
      IsCompact K → K ⊆ conf n → ∀ p : ℕ, 1 ≤ p → ∀ B : ℝ, 0 < B →
        _root_.YM.FVA2.GradedFar.AppointedTwoFiledPublicRows.UnselectedIncome.{u,v}
          g hg periods mono e hout p K B) :
    Window.Regained (V.{u} g hg periods mono).pupil.last ((V.{u} g hg periods mono).Post (N g hg))
      (V.{u} g hg periods mono).pupil.P (Measure.outlook (N g hg).scheme (N g hg).criterion)
      ((V.{u} g hg periods mono).T (N g hg)) n hin hout := by
  apply AppointedRaisedReader.regained.{u} g hg periods mono n hin hout
  intro e he K hK hx a l q
  exact _root_.YM.FVA2.GradedFar.AppointedRaisedNumerator.coordinate.{u,v} g hg periods mono
    hn e hout q hK hx a l (incomes he hK hx)

end YM.Integration.GradedFar.AppointedRaisedReceives

