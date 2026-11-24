import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedRaisedReceives
import YM.Integration.WilsonGraphSingletonNearEveryGrade

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace YM.FVA2.GradedFar.AppointedOneNearPublic
noncomputable section
open Filter Function Real Set MeasureTheory PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window OPE Orbits Physical
open YangMills YM.Answer.ContinuumLimit YM.Integration Asymptotics
open scoped Topology BigOperators Classical ContDiff

universe u v
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)
private abbrev N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev heat := ElectedMeasurement.clock (V.{u} g hg periods strict) (N g hg)


open AppointedRaisedNumerator

theorem value (d : Fin 1 → ℕ) (h q : ℕ) {K : Set (Points 1)}
    (hK : IsCompact K) (hx : K ⊆ conf 1) (L : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ o : E4, ∀ x ∈ K,
      ∀ u : Inputs g.core d, Within L u →
        Ball (D*(heat.{u} g hg periods strict r)^(q+1))
          ((show Sec g.core h from (AppointedOrdinaryPacket.measurement hg (V.{u} g hg periods strict)
            (N g hg) (Q.{u} g hg)).wilsonOPE r h (fun i => ⟨d i,u i⟩) o x) -
           Wave.cropped (N g hg) (Q.{u} g hg).MS x u h q (heat.{u} g hg periods strict r)) := by
  obtain ⟨frame,history⟩ := AppointedTwoFiledPayments.electedCosts.{u} g hg periods strict
  obtain ⟨D,hD,paid⟩ := Physical.AppointedTwoRoundedRows.measuredAtPositiveCrops
    (Q.{u} g hg).matching (AppointedPhysicalWindowAndPhase.electedClock.{u} g hg periods strict)
    history frame hK hx L (by decide : 0 < 1) d h q
    (fun p _ B hB => AppointedOneNear.everyGrade.{u} g hg periods strict d h p K {RootG} hK
      isCompact_singleton (singleton_subset_iff.mpr ok_wall) one_pos hB)
    (fun p B hB => AppointedCenteredRounded.roundedAt.{u} g hg periods strict h p {RootG}
      isCompact_singleton (singleton_subset_iff.mpr ok_wall) one_pos hB)
  refine ⟨D,hD,?_⟩
  filter_upwards [paid] with r hr
  intro o x hx₀ u hu
  rw [AppointedTwoFiledPublicRows.readerValue.{u} g hg periods strict d u h r (none,o) x]
  exact hr (none,o) x hx₀ u hu

theorem coordinate (e : Fin 1 → ℕ) (h q : ℕ) {K : Set (Points 1)}
    (hK : IsCompact K) (hx : K ⊆ conf 1) (a : (i : Fin 1) → Sec g.core (e i)) (l : Toon g.core h) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ o : E4, ∀ x ∈ K,
      ‖coord l (show Sec g.core h from (AppointedOrdinaryPacket.measurement hg (V.{u} g hg periods strict)
        (N g hg) (Q.{u} g hg)).wilsonOPE r h (fun i => ⟨e i,a i⟩) o x) -
        (∑ j ∈ Finset.range (q+1), (heat.{u} g hg periods strict r : ℂ)^j *
          coeff j (filedSeries (N g hg) x a l))‖ ≤
        D * (heat.{u} g hg periods strict r)^(q+1) := by
  obtain ⟨L,hL⟩ := finiteInputBound a
  obtain ⟨D,hD,paid⟩ := value.{u} g hg periods strict e h q hK hx L
  refine ⟨D,hD,?_⟩
  filter_upwards [paid] with r hr
  intro o x hx₀
  have original := hr o x hx₀ a hL l
  have sub (b c : Sec g.core h) : coord l (b-c) = coord l b - coord l c := by
    simp [coord]
  rw [sub, prescribed (N g hg) (Q.{u} g hg).MS (Q.{u} g hg).matching] at original
  simpa only [YM.FVA2.GradedFar.crop_eq] using original


theorem regained (hin hout : ℕ) :
    _root_.YM.Integration.GradedFar.Window.Regained (V.{u} g hg periods strict).pupil.last
      ((V.{u} g hg periods strict).Post (N g hg)) (V.{u} g hg periods strict).pupil.P
      (Measure.outlook (N g hg).scheme (N g hg).criterion) ((V.{u} g hg periods strict).T (N g hg))
      1 hin hout := by
  apply _root_.YM.Integration.GradedFar.AppointedRaisedReader.regained.{u} g hg periods strict 1 hin hout
  intro e _ K hK hx a l q
  exact coordinate.{u} g hg periods strict e hout q hK hx a l

end
end YM.FVA2.GradedFar.AppointedOneNearPublic
