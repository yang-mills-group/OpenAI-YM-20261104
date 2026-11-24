import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedDualWord
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedCartesianWords

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section
namespace YM.Integration.GradedFar.AppointedFullOrdinaryJet
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



theorem scalarSmooth {G : Gauge} {n h : ℕ} {X : Set (Points n)}
    (out : Module.Dual ℂ (Sec G h)) (f : Points n → Sec G h)
    (coords : ∀ a : Toon G h, ContDiffOn ℝ ∞ (fun y => coord a (f y)) X) :
    ContDiffOn ℝ ∞ (fun y => out (f y)) X := by
  have original : ContDiffOn ℝ ∞ (fun y => ∑ a : Toon G h, out (theory a) * coord a (f y)) X :=
    ContDiffOn.sum (fun a _ => contDiffOn_const.mul (coords a))
  apply original.congr
  intro y _
  rw [AppointedPaperOrdinary.wholeDual out (f y)]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _
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

theorem allOrders {n ℓ h : ℕ} {d : Fin n → ℕ} {K : Set (Points n)}
    (compact : IsCompact K) (sep : K ⊆ conf n)
    (prior : M2Continuation.Prior (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.last (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg))
    (traced : LogTrace (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.last (_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).pupil.P.port)
    (hd : AppointedH140Through ℓ d) (hh : h ≤ ℓ) (q : ℕ) (ν : ℝ)
    (out : Module.Dual ℂ (Sec g.core h)) (j : ℕ)
    (smooth : ∀ᶠ r in trail, ∀ o x, x ∈ K → ∀ v : AppointedH140Inputs g.core d, Box v 1 →
      ∃ X : Set (Points n), IsOpen X ∧ x ∈ X ∧
        (∀ a : Toon g.core h, ContDiffOn ℝ ∞
          (fun y => coord a (actualField.{u} g hg periods mono r o v y)) X) ∧
        (∀ a : Toon g.core h, ContDiffOn ℝ ∞
          (fun y => coord a (actualCrop.{u} g hg periods mono q ν r v y)) X)) :

    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r in trail, ∀ o x, x ∈ K → ∀ v : AppointedH140Inputs g.core d, Box v 1 →
      ∀ l : Fin (j+1),
        ‖iteratedFDeriv ℝ l.val (fun y => out (actualField.{u} g hg periods mono r o v y)) x -
          iteratedFDeriv ℝ l.val (fun y => out (actualCrop.{u} g hg periods mono q ν r v y)) x‖ ≤
            A * |((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).T (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) r) ^ (q+1)| := by
  let U := E4 × {x : Points n // x ∈ K} × {v : AppointedH140Inputs g.core d // Box v 1}
  let physical (r : ℝ) (u : U) (y : Points n) :=
    out (actualField.{u} g hg periods mono r u.1 u.2.2.val y)
  let filed (r : ℝ) (u : U) (y : Points n) :=
    out (actualCrop.{u} g hg periods mono q ν r u.2.2.val y)
  let jets (r : ℝ) (u : U) (l : Fin (j+1)) :=
    iteratedFDeriv ℝ l.val (physical r u) u.2.1.val - iteratedFDeriv ℝ l.val (filed r u) u.2.1.val
  let err (r : ℝ) (_ : U) := |((_root_.YM.Integration.WilsonGraphPaperPublication.publicPick.{u} g hg (_root_.YM.Answer.ContinuumLimit.ElectedPublication.order periods mono)).T (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) r) ^ (q+1)|
  have one : ∀ (l : Fin (j+1)) (w : Fin l.val → Fin n × Axis),
      ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ r in trail, ∀ u : U,
        ‖jets r u l (fun i => WilsonGraphCartesianJetBound.axis (w i))‖ ≤ D * err r u := by
    intro l w
    obtain ⟨D,hD,paid⟩ := AppointedDualWord.onPaper.{u} g hg periods mono compact sep prior traced
      hd hh q ν out (AppointedCartesianWords.trace l.val w) smooth
    refine ⟨D,hD,?_⟩
    filter_upwards [smooth, paid] with r hr hp
    intro u
    obtain ⟨X,hX,inside,hf,hg'⟩ := hr u.1 u.2.1.val u.2.1.property u.2.2.val u.2.2.property
    have h := hp u.1 u.2.1.val u.2.1.property u.2.2.val u.2.2.property
    have fSmooth : ContDiffOn ℝ ∞ (physical r u) X := scalarSmooth out _ hf
    have gSmooth : ContDiffOn ℝ ∞ (filed r u) X := scalarSmooth out _ hg'
    change ‖δ (AppointedCartesianWords.trace l.val w) (physical r u) u.2.1.val -
      δ (AppointedCartesianWords.trace l.val w) (filed r u) u.2.1.val‖ ≤ _ at h
    rw [AppointedCartesianWords.onWord hX fSmooth inside l.val w,
      AppointedCartesianWords.onWord hX gSmooth inside l.val w] at h
    exact h.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hD)
  obtain ⟨A,hA,paid⟩ := WilsonGraphCartesianJetBound.uniform (I := fun _ : ℝ => U)
    trail j jets err (fun r u => abs_nonneg _) one
  refine ⟨A,hA,?_⟩
  filter_upwards [paid] with r hr
  intro o x hx v hv l
  exact hr (o, ⟨x,hx⟩, ⟨v,hv⟩) l

end YM.Integration.GradedFar.AppointedFullOrdinaryJet
end

