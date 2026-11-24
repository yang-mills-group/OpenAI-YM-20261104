import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedOrdinaryPacket
import YM.Integration.WilsonGraphPaperCorrelations
import YM.GradedFar.Age

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section
namespace YM.Integration.GradedFar.AppointedPaperOrdinary
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

private abbrev submitted {n : ℕ} (d : Fin n → ℕ) (v : AppointedH140Inputs g.core d) :
    Fin n → Σ e : ℕ, (YangMills.maxwellReference g).sector e :=
  fun i => ⟨d i, v i⟩

theorem packet {n : ℕ} (d : Fin n → ℕ) (v : AppointedH140Inputs g.core d)
    (h : ℕ) (r : ℝ) (o : E4) (x : Points n) :
    (_root_.YM.Answer.ContinuumLimit.AppointedOrdinaryPacket.measurement hg (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (_root_.YM.Integration.WilsonGraphPaperPublication.perspective.{u} g hg)).wilsonOPE r h (submitted g d v) o x =
      GradedFar.packet (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.last ((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).Post (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.P h o r x v := by
  exact AppointedOrdinaryPacket.packet hg (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (_root_.YM.Integration.WilsonGraphPaperPublication.perspective.{u} g hg) h d v r o x

theorem allWords {n ℓ h : ℕ} {d : Fin n → ℕ} {K : Set (Points n)}
    (compact : IsCompact K) (sep : K ⊆ conf n)
    (prior : M2Continuation.Prior (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.last (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg))
    (traced : LogTrace (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.last (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.P.port)
    (hd : AppointedH140Through ℓ d) (hh : h ≤ ℓ) (q : ℕ) (ν : ℝ) :
    (∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ r in trail, ∀ o x, x ∈ K → ∀ v : AppointedH140Inputs g.core d,
      Box v 1 → width ((show Sec g.core h from (_root_.YM.Answer.ContinuumLimit.AppointedOrdinaryPacket.measurement hg (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (_root_.YM.Integration.WilsonGraphPaperPublication.perspective.{u} g hg)).wilsonOPE r h (submitted g d v) o x) -
        msVector (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (_root_.YM.Integration.WilsonCapturedPhysicalMSDatum.original g.core) ν v x q h ((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).T (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) r)) ≤ D * ((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).T (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) r)^(q+1)) ∧
    ∀ (L : TraceOrder n) (a : Toon g.core h), ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ r in trail,
      ∀ o x, x ∈ K → ∀ v : AppointedH140Inputs g.core d, Box v 1 →
        ‖δ L (fun y => coord a ((_root_.YM.Answer.ContinuumLimit.AppointedOrdinaryPacket.measurement hg (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (_root_.YM.Integration.WilsonGraphPaperPublication.perspective.{u} g hg)).wilsonOPE r h (submitted g d v) o y)) x -
          δ L (fun y => coord a (msVector (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (_root_.YM.Integration.WilsonCapturedPhysicalMSDatum.original g.core) ν v y q h ((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).T (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) r))) x‖
          ≤ D * ((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).T (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) r)^(q+1) := by
  have paid := M2Continuation.ordinary_ope (U := (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.last) (J := (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.J)
    (lead := (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.VFrame.2) (N := (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) (Q := (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.P)
    (M := (_root_.YM.Integration.WilsonGraphPaperPublication.perspective.{u} g hg).MS) (matched := (_root_.YM.Integration.WilsonGraphPaperPublication.perspective.{u} g hg).matching) (ν := ν) (hp := prior) (HL := traced)
    (hK := compact) (hx := sep) hd hh q
  rw [WilsonGraphPaperPublication.nominated.{u} g hg] at paid
  simpa only [packet g hg periods mono] using paid

theorem wholeDual {G : Gauge} {h : ℕ} (out : Module.Dual ℂ (Sec G h))
    (v : Sec G h) :
    out v = ∑ c : Toon G h, (_root_.YM.MS.Theater.Daylight (Press.portDeck G) h).repr v c * out (theory c) := by
  conv_lhs => rw [← Dframe.all_sig v]
  simp only [map_sum, map_smul, smul_eq_mul]

end YM.Integration.GradedFar.AppointedPaperOrdinary
end

