import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedMeasuredJetMass
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedRaisedReceives
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedOneNearPublic
import YM.Integration.WilsonGraphAppointedOrdinaryWordMass
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedAllFieldCharts
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedFullOrdinaryJet
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedDerivativeBook
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedDerivativeFrames
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedCartesianWords

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section
namespace YM.Integration.GradedFar.AppointedMeasuredJetPurchases
open Function Filter Set PowerSeries MeasureTheory Metric
open Wilson RG Source Extraction Table Spec PhysicalNext.Repeat.Legato RG17 FullVolume
open Climb Trace.Pilot PhysMS OPE OPE.Orbits
open XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open MS MS.Native MS.Land MS.Fleet
open Dframe O O.Score O.Enh FVA2.GradedFar
open Batch Auth Tariff Tariff.Playbill Tariff.Sunshine
open Answer.ContinuumLimit Answer.ContinuumLimit.Vision
open scoped Topology BigOperators Classical ContDiff

universe u v
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
theorem incomes {n h : ℕ} {d : Fin n → ℕ} {K : Set (Points n)}
    (compact : IsCompact K) (sep : K ⊆ conf n)
    (hn : 0 < n)
    (incomes : ∀ (hin : ℕ) {e : Fin n → ℕ}, AppointedH140Through hin e → ∀ {L : Set (Points n)},
      IsCompact L → L ⊆ conf n → ∀ p : ℕ, 1 ≤ p → ∀ B : ℝ, 0 < B →
        _root_.YM.FVA2.GradedFar.AppointedTwoFiledPublicRows.UnselectedIncome.{u,v}
          g hg periods mono e h p L B)
    (q j : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r in trail, ∀ (o : E4) (x : Points n), x ∈ K →
      ∀ (v : AppointedH140Inputs g.core d) (out : Module.Dual ℂ (Sec g.core h)),
      (∀ z, ‖out z‖ ≤ YangMills.Matching.sectorMass (B := YangMills.maxwellReference g) z) →
      ∀ l : Fin (j+1),
      ‖iteratedFDeriv ℝ l.val (fun y => out (actualField.{u} g hg periods mono r o v y)) x -
        iteratedFDeriv ℝ l.val (fun y => out (actualCrop.{u} g hg periods mono q (FVA2.Teller.logNu 1) r v y)) x‖ ≤
          A * inputMass g (d := d) v * |((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).T (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) r)|^(q+1) := by
  exact AppointedMeasuredJetMass.allOrders.{u} g hg periods mono compact sep
    (fun hin => AppointedRaisedReceives.onIncomes.{u,v} g hg periods mono hn hin h (incomes hin)) q j

theorem oneNear {h : ℕ} {d : Fin 1 → ℕ} {K : Set (Points 1)}
    (compact : IsCompact K) (sep : K ⊆ conf 1)
    (q j : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r in trail, ∀ (o : E4) (x : Points 1), x ∈ K →
      ∀ (v : AppointedH140Inputs g.core d) (out : Module.Dual ℂ (Sec g.core h)),
      (∀ z, ‖out z‖ ≤ YangMills.Matching.sectorMass (B := YangMills.maxwellReference g) z) →
      ∀ l : Fin (j+1),
      ‖iteratedFDeriv ℝ l.val (fun y => out (actualField.{u} g hg periods mono r o v y)) x -
        iteratedFDeriv ℝ l.val (fun y => out (actualCrop.{u} g hg periods mono q (FVA2.Teller.logNu 1) r v y)) x‖ ≤
          A * inputMass g (d := d) v * |((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).T (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) r)|^(q+1) := by
  exact AppointedMeasuredJetMass.allOrders.{u} g hg periods mono compact sep
    (fun hin => _root_.YM.FVA2.GradedFar.AppointedOneNearPublic.regained.{u} g hg periods mono hin h) q j

end YM.Integration.GradedFar.AppointedMeasuredJetPurchases
end

