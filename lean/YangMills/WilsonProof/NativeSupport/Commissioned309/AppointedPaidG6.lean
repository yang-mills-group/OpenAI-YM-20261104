import YangMills.WilsonProof.NativeSupport.Commissioned309.AppointedPreAmple
import YM.GradedFar.Elected.Prospects
import YM.Integration.WilsonGraphPaperCorrelations

namespace YM.FVA2.GradedFar.Appointed1860G6

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


theorem retained : PreElectedPublication.Retained
      (WilsonGraphPaperPublication.construction.{u} g hg) (fun _ => True)
      (ElectedPublication.order p hp) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)) :=
    (((WilsonGraphPaperPublication.rowBefore.{u} g hg).choose_spec.2.2
      (fun _ => True) (fun _ _ _ => True.intro)).choose_spec.1 _)

theorem paid {n m : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    {X : Set (Points n)} {Y : Set (Points m)}
    (hX : IsCompact X) (hx : X ⊆ conf n) (hY : IsCompact Y) (hy : Y ⊆ Outside m)
    (h : ℕ) (L R' : ℝ) :
    ∀ᶠ k : ℝ in atTop, ∃ D : ℝ, 0 < D ∧ ∀ C B : ℝ, 0 < C → 0 < B →
      ∀ᶠ (w : Window) in windows (upper g.core C B), ∀ o : View ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last),
      ∀ x ∈ X, ∀ y ∈ Y, ∀ (u : Inputs g.core d), Within L u →
      ∀ (v : Inputs g.core e), Within R' v → ∀ (a : Sec g.core h), Ball 1 a →
        Physical.Owed ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.P (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J)) k D h w.len w.Coarse o x y u v a :=
  Elected.G6 (d:=d) (e:=e) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).MS (WilsonGraphPaperPublication.perspective.{u} g hg).matching ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.VFrame.2
    (Appointed1859PreAmple.ample (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.P (retained g hg p hp).2.2.2.2.1
    hX hx hY hy h L R'

theorem gridRows (prior : Round.Grid (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) (Elected.Wframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J))) :
    Physical.SourceCost (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J)) (WilsonPositionHomogeneousFrame.reading ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) :=
  Elected.G9_value (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg).MS (WilsonGraphPaperPublication.perspective.{u} g hg).matching ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.VFrame.2
    (Appointed1859PreAmple.ample (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)) (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.P (retained g hg p hp).2.2.2.2.1 prior

theorem nearOne (prior : Round.Grid (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) (Elected.Wframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J))) {n : ℕ} (d : Fin n → ℕ) (e : Fin 1 → ℕ)
    (q : ℕ) (X : Set (Points n)) (Y : Set (Points 1))
    (hX : IsCompact X) (hx : X ⊆ conf n) (hY : IsCompact Y) (hy : Y ⊆ Outside 1)
    (B C : ℝ) (hB : 0 < B) (hC : 0 < C) :
    RoundedAt (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (Physical.Y0 ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J)) d e) (upper g.core C B) X Y
      (WilsonPositionHomogeneousFrame.reading ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) q :=
  gridRows g hg p hp prior n 1 d e q X Y hX hx hY hy B C hB hC

theorem centerOne (prior : Round.Grid (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) (Elected.Wframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J))) (h : ℕ) (e : Fin 1 → ℕ)
    (q : ℕ) (X Y : Set (Points 1)) (hX : IsCompact X) (hx : X ⊆ conf 1)
    (hY : IsCompact Y) (hy : Y ⊆ Outside 1) (B C : ℝ) (hB : 0 < B) (hC : 0 < C) :
    RoundedAt (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (Physical.Y0 ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) (Elected.Hframe (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J)) (fun _ : Fin 1 => h) e) (upper g.core C B) X Y
      (WilsonPositionHomogeneousFrame.reading ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.last) ((WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order p hp)).pupil.J) (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)) q :=
  gridRows g hg p hp prior 1 1 (fun _ => h) e q X Y hX hx hY hy B C hB hC

end Paper
end
end YM.FVA2.GradedFar.Appointed1860G6

