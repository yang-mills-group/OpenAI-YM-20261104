import YM.Integration.WilsonGraphSingletonNearGrade
import YM.Integration.WilsonGraphSingletonNearCompact
import YM.Integration.WilsonGraphCenteredRoundedSource
import YM.GradedFar.Round.G9

/-! The filed one-near continuum numerator on its original uncentered compact, all growing
    separation windows and the one far reader at the original output grade. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.FVA2.GradedFar.AppointedOneNear

open Function Filter Finset Set Real PowerSeries Growth Continuation Window
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS MS.Book MS.Land Scale Register O O.Enh O.Score Dframe
open YangMills YangMills.Matching YM.Answer.ContinuumLimit YM.Integration YM.OPE YM.OPE.Orbits
open AppointedMixedFarRow
open scoped Topology BigOperators Classical

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)
private abbrev N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev H := Elected.Hframe (N g hg) (V.{u} g hg periods strict).pupil.last (V.{u} g hg periods strict).pupil.J
private abbrev heat := ElectedMeasurement.clock (V.{u} g hg periods strict) (N g hg)
private abbrev grade (h : ℕ) := fun _ : Fin 1 => h

include periods strict in
theorem rowAtGrade (h : ℕ) (s : ℝ) (x y : YM.Points 1)
    (u v : Inputs g.core (grade h)) (safe : placement s (0,exterior s x y) ∈ YM.conf 2) :
    Continuation.row (N g hg) x u y v s =
      Continuation.row (N g hg) (0 : YM.Points 1) u (exterior s x y) v s := by
  have all := formal g hg periods strict (fun _ : Fin (1+1) => h) (Fin.append u v) s x y safe
  simpa only [AppointedMixedFarRow.series,Fin.append_left,Fin.append_right] using all

/-- The complete original positive numerator receipt for one near slot and its one far peer. -/
theorem roundedAt (d : Fin 1 → ℕ) (h p : ℕ) (hd : ∀ i, d i ≤ h)
    (K S : Set (YM.Points 1)) (near : IsCompact K) (far : IsCompact S)
    (outside : S ⊆ O.Enh.Outside 1) {C B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    RoundedAt (N g hg) (Physical.Y0 (V.{u} g hg periods strict).pupil.last
      (H.{u} g hg periods strict) d (grade h)) (upper g.core C B) K S
      (heat.{u} g hg periods strict) p := by
  intro L R
  obtain ⟨lifted,bounds⟩ := Physical.Round.hosts (G := g.core) d L hd
  obtain ⟨T,compact,permitted,geometry⟩ := compactExterior near far outside (upper g.core C B)
  obtain ⟨D,hD,e,center⟩ := AppointedCenteredRounded.boundedRows.{u} g hg periods strict h p T
    compact permitted hC hB lifted R
  have changeGrade := (windows_short (upper g.core C B)).eventually
    (physicalCap.{u} (e := grade h) g hg periods strict hd)
  refine ⟨D,hD,e,?_⟩
  filter_upwards [geometry,center,changeGrade] with w stays paid raiseAt
  intro i x hx y hy u hu v hv
  let t := exterior w.2 x y
  have ht : t ∈ T := stays x hx y hy
  have ok : placement w.2 ((0 : YM.Points 1),t) ∈ YM.conf 2 :=
    O.Enh.lives (-w.2) (permitted ht)
  have before := stageSeparated w.2 x y ok
  let liftedU : Inputs g.core (grade h) := installedInputs hd u
  have bound := (paid (i.1,i.2+w.1 • x 0) t ht liftedU (bounds u hu) v hv).1
  have atGrade := raiseAt w.2 i.1 i.2 x y before u v
  have place := physical (V.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
    w i.1 i.2 x y liftedU v
  have formalGrade := formalCap g hg hd (fun _ : Fin 1 => le_rfl) w.2 x u y v before
  have formalPlace := rowAtGrade g hg periods strict h w.2 x y liftedU v ok
  have observed : Physical.Y0 (V.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
      d (grade h) w i x y u v =
      Physical.Y0 (V.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
        (grade h) (grade h) w (i.1,i.2+w.1 • x 0) 0 t liftedU v :=
    atGrade.trans place
  have coefficients : Continuation.row (N g hg) x u y v (Window.sep w) =
      Continuation.row (N g hg) (0 : YM.Points 1) liftedU t v (Window.sep w) :=
    formalGrade.trans formalPlace
  rw [observed,coefficients]
  exact bound

end YM.FVA2.GradedFar.AppointedOneNear
end

