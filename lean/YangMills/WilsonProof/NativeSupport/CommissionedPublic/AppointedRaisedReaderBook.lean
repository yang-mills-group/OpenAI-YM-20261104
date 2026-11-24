import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedPaperOrdinary

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section
namespace YM.Integration.GradedFar.AppointedRaisedReader
open Function Filter Set PowerSeries MeasureTheory Metric
open Wilson RG Source Extraction Table Spec PhysicalNext.Repeat.Legato RG17 FullVolume
open Climb Trace.Pilot PhysMS OPE OPE.Orbits
open XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open MS MS.Native MS.Land MS.Fleet
open Dframe O O.Score O.Enh FVA2.GradedFar
open Batch Auth Tariff Tariff.Playbill Tariff.Sunshine
open Answer.ContinuumLimit Answer.ContinuumLimit.Vision
open scoped Topology BigOperators Classical


universe u
variable (g : YangMills.GaugeGroup) (hg : g.IsSimple)
variable (periods : ℕ → ℕ) (mono : StrictMono periods)
private abbrev V := _root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg
  (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)
private abbrev Q := _root_.YM.Integration.WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev W := _root_.YM.Answer.ContinuumLimit.AppointedOrdinaryPacket.measurement hg
  (V.{u} g hg periods mono) (N g hg) (Q.{u} g hg)

abbrev commonSeries {n h : ℕ} {e : Fin n → ℕ} (a : (i : Fin n) → Sec g.core (e i))
    (x : Points n) (l : Toon g.core h) : PowerSeries ℂ :=
  ∑ b : (i : Fin n) → Toon g.core (e i), PowerSeries.C (∏ i, coord (b i) (a i)) *
    O.Canon.FarCoefficients (Measure.outlook (N g hg).scheme (N g hg).criterion)
      (fun i => Dframe.flash (b i)) x (Dframe.flash l)

theorem cargo {n h : ℕ} {e : Fin n → ℕ} (a : (i : Fin n) → Sec g.core (e i))
    (x : Points n) (l : Toon g.core h) :
    Window.Cargo (Measure.outlook (N g hg).scheme (N g hg).criterion) x a l =
      commonSeries g hg a x l := rfl

/-- Each income is used for the fixed number of near inputs, after the genuine change of grades. -/
def PublicValues (n hin hout : ℕ) : Prop :=
  ∀ {e : Fin n → ℕ}, AppointedH140Through hin e → ∀ (K : Set (Points n)), IsCompact K → K ⊆ conf n →
    ∀ (a : (i : Fin n) → Sec g.core (e i)) (l : Toon g.core hout) (q : ℕ),
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in trail, ∀ o : E4, ∀ x ∈ K,
      ‖coord l (show Sec g.core hout from (W.{u} g hg periods mono).wilsonOPE r hout
        (fun i => ⟨e i,a i⟩) o x) -
        (∑ j ∈ Finset.range (q+1), ((V.{u} g hg periods mono).T (N g hg) r : ℂ)^j *
          coeff j (commonSeries g hg a x l))‖ ≤ D*((V.{u} g hg periods mono).T (N g hg) r)^(q+1)

theorem regained (n hin hout : ℕ) (values : PublicValues.{u} g hg periods mono n hin hout) :
    Window.Regained (V.{u} g hg periods mono).pupil.last ((V.{u} g hg periods mono).Post (N g hg))
      (V.{u} g hg periods mono).pupil.P (Measure.outlook (N g hg).scheme (N g hg).criterion)
      ((V.{u} g hg periods mono).T (N g hg)) n hin hout := by
  intro e he K hK hx l a
  refine ⟨fun i => ?_, fun q => ?_⟩
  · obtain ⟨D,hd⟩ := hK.exists_bound_of_continuousOn
      ((Window.cargo_cont (N g hg) (Q.{u} g hg).MS (Q.{u} g hg).matching l a i).mono hx)
    exact FVA2.GradedFar.Cart.Charge.cap ⟨D, fun x => hd x.2.val x.2.property⟩
  · obtain ⟨D,hD,original⟩ := values he K hK hx a l q
    refine ⟨D,hD.le,?_⟩
    filter_upwards [original] with r hr
    intro i
    have price := hr i.1 i.2.val i.2.property
    rw [AppointedPaperOrdinary.packet.{u} g hg periods mono e a hout r i.1 i.2.val] at price
    rw [Window.alarm, crop_eq, cargo g hg a i.2.val l]
    exact price.trans (mul_le_mul_of_nonneg_left (by rw [← abs_pow]; exact le_abs_self _) hD.le)

end YM.Integration.GradedFar.AppointedRaisedReader

