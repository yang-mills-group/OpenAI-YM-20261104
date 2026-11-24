import YangMills.WilsonProof.NativeSupport.Commissioned309.AppointedPaidG6

namespace YM.FVA2.GradedFar.AppointedPhysicalWindowAndPhase

set_option quotPrecheck false
set_option maxHeartbeats 4000000
noncomputable section
open Filter Function Real Set MeasureTheory
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window OPE Orbits Physical
open YM.Answer.ContinuumLimit YM.Integration
open scoped Topology BigOperators Classical ContDiff

section Paper

universe u
variable (g : YangMills.GaugeGroup) (hg : g.IsSimple) (p : ℕ → ℕ) (hp : StrictMono p)


theorem earned : Physical.Earned (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).MS (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last (Elected.Wframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J) (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J) (WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) :=
  Elected.G1_lane (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).MS (WilsonGraphPaperPublication.perspective.{u} g hg).matching (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.VFrame.2
    (Appointed1859PreAmple.ample (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg))

theorem electedClock :
    Tendsto (fun r : ℝ => (WilsonPositionHomogeneousFrame.reading (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) r / gYM g.core r) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
  (earned.{u} g hg p hp).clock

theorem farAllowances (q d : ℕ) {C B : ℝ} (hc : 0 < C) (hb : 0 < B) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ s : ℝ, 0 ≤ s → Real.exp s ≤ C * (gYM g.core r) ^ (-B) →
      ‖Zenith (Physical.next (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J) d) r s‖ ≤ 2 * (Real.exp s) ^ d ∧
      ‖Zenith (Physical.next (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J) d) (r * Real.exp s) (-s)‖ ≤ 2 :=
  ((earned.{u} g hg p hp).main q d hc hb).2

theorem forwardAtWindow (d : ℕ) (r s : ℝ) :
    Physical.next (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J) d r s = ((Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J) (r * Real.exp s) d).trans ((Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J) r d).symm := rfl

theorem reverseAtWindow (d : ℕ) (r s : ℝ) :
    Physical.next (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J) d (r * Real.exp s) (-s) =
      ((Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J) r d).trans ((Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J) (r * Real.exp s) d).symm := by
  unfold Physical.next Moving.resize
  rw [Real.exp_neg, mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.exp_pos s)), mul_one]

theorem phaseRows {n m : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    {X : Set (Points n)} {Y : Set (Points m)}
    (hX : IsCompact X) (hx : X ⊆ conf n) (hY : IsCompact Y) (hy : Y ⊆ Outside m)
    (h : ℕ) (L R' : ℝ) :
    ∀ᶠ k : ℝ in atTop, ∃ D : ℝ, 0 < D ∧ ∀ C B : ℝ, 0 < C → 0 < B →
      ∀ᶠ (w : Window) in windows (upper g.core C B), ∀ o : View ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last),
      ∀ x ∈ X, ∀ y ∈ Y, ∀ (u : Inputs g.core d), Within L u →
      ∀ (v : Inputs g.core e), Within R' v → ∀ (a : Sec g.core h), Ball 1 a →
        let total (i : View (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) := Physical.Yactual (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J) w.len w.Coarse i x y u v
        let column (i : View (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) (b : Sec g.core h) :=
          Physical.Dactual (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J) w.len w.Coarse i y v b
        let delta (b : Sec g.core h) := column o b - column (none, o.2) b
        ‖total o - total (none, o.2)‖ + ‖delta a‖ + weigh h delta ≤
          D * (gYM g.core w.len) ^ (-k) * w.Coarse := by
  filter_upwards [Appointed1860G6.paid.{u} (d:=d) (e:=e) g hg p hp hX hx hY hy h L R'] with k hk
  obtain ⟨D, hD, sale⟩ := hk
  refine ⟨D, hD, ?_⟩
  intro C B hc hb
  filter_upwards [sale C B hc hb] with w hw
  intro o x hxx y hyy u hu v hv a ha
  exact (hw o x hxx y hyy u hu v hv a ha).2.2

end Paper
end
end YM.FVA2.GradedFar.AppointedPhysicalWindowAndPhase

