import YM.Integration.WilsonGraphCenteredFarAppointedOriginalPrice

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCenteredRounded

open Filter Real Growth Continuation
open Register MS MS.Native MS.Land MS.Book MS.Book.Program
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Reg.Point
open YangMills YM.Answer.ContinuumLimit YM.Integration
open scoped Topology BigOperators Classical

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)
private abbrev Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev H := Elected.Hframe (Z g hg) (V.{u} g hg periods strict).pupil.last
  (V.{u} g hg periods strict).pupil.J
private abbrev heat := ElectedMeasurement.clock (V.{u} g hg periods strict) (Z g hg)
private abbrev grade (h : ℕ) := fun _ : Fin 1 => h

/-- Both original single-site block prices on the native growing windows, uniformly
over the two coordinate balls, all published viewers, and the exterior compact set. -/
theorem boundedRows (h p : ℕ) (S : Set (YM.Points 1)) (compact : IsCompact S)
    (outside : S ⊆ O.Enh.Outside 1) {C B : ℝ} (hC : 0 < C) (hB : 0 < B) (L R : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∃ e : ℕ, ∀ᶠ w in Window.windows (upper g.core C B),
      ∀ (i : Physical.View (V.{u} g hg periods strict).pupil.last) (y : YM.Points 1), y ∈ S →
      ∀ (u : Inputs g.core (grade h)), Within L u → ∀ (v : Inputs g.core (grade h)), Within R v →
        let cost := D * (gYM g.core w.len)^(p+1) * (1+w.sep)^e
        ‖Physical.Y0 (V.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
          (grade h) (grade h) w i 0 y u v -
          crop p (heat.{u} g hg periods strict w.len) (Continuation.row (Z g hg) 0 u y v w.sep)‖ ≤ cost ∧
        ‖Physical.Dactual (V.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
          w.len w.Coarse i y v (u 0) -
          crop p (heat.{u} g hg periods strict w.len) (Dx (Z g hg) (Q.{u} g hg).MS y v w.sep (u 0))‖ ≤ cost := by
  let K : Set (YangMills.Points 2) := outgoing '' S
  have hcompact : IsCompact K := compact.image (O.Enh.continual continuous_const continuous_id)
  have hsafe : K ⊆ YM.conf 2 := by
    rintro _ ⟨y,hy,rfl⟩
    exact outside hy
  obtain ⟨A,hA,e,paid⟩ := AppointedOriginalOperand.onWindow.{u} g hg periods strict h p K hcompact hsafe hC hB
  let D := 1 + A * (max L 0 * max R 0)
  have hLR : 0 ≤ max L 0 * max R 0 := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have hA' : 0 ≤ A * (max L 0 * max R 0) := mul_nonneg hA hLR
  refine ⟨D,by dsimp [D]; linarith,e,(Window.windows_eventually _ _).2 ⟨0,?_⟩⟩
  filter_upwards [paid, positive_g (_root_.IssuedMaxwell.ElectedPrescription.simple g hg)] with r hr positive
  intro s hs window i y hy u hu v hv
  have atCenter : outgoing y = WithLp.toLp 2 ![0,y 0] := by
    apply congrArg (WithLp.toLp 2)
    funext j
    fin_cases j <;> rfl
  have member : WithLp.toLp 2 ![0,y 0] ∈ K := atCenter ▸ Set.mem_image_of_mem outgoing hy
  obtain ⟨allNear,mixed⟩ := hr s hs window (u 0) (v 0) i.1 i.2 y member
  have uu : (fun _ : Fin 1 => u 0) = u := by
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rfl
  have vv : (fun _ : Fin 1 => v 0) = v := by
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rfl
  rw [uu,vv] at allNear
  rw [vv] at mixed
  have left : ‖chair g.core h (u 0)‖ ≤ max L 0 :=
    (chair_ball (u 0) (le_max_right _ _)).mp fun b => (hu 0 b).trans (le_max_left _ _)
  have right : ‖chair g.core h (v 0)‖ ≤ max R 0 :=
    (chair_ball (v 0) (le_max_right _ _)).mp fun b => (hv 0 b).trans (le_max_left _ _)
  have coeff : A * (‖chair g.core h (u 0)‖ * ‖chair g.core h (v 0)‖) ≤ D :=
    (mul_le_mul_of_nonneg_left (mul_le_mul left right (norm_nonneg _) (le_max_right _ _)) hA).trans
      (by dsimp [D]; linarith)
  have total := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right coeff (pow_nonneg positive.le (p+1)))
    (pow_nonneg (by linarith : 0 ≤ 1+s) e)
  exact ⟨allNear.trans total,mixed.trans total⟩

/-- The centered second source call of the original #309 comparison on each published period. -/
theorem roundedAt (h p : ℕ) (S : Set (YM.Points 1)) (compact : IsCompact S)
    (outside : S ⊆ O.Enh.Outside 1) {C B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    Continuation.RoundedAt (Z g hg)
      (Physical.Y0 (V.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict) (grade h) (grade h))
      (upper g.core C B) ({0} : Set (YM.Points 1)) S (heat.{u} g hg periods strict) p := by
  intro L R
  obtain ⟨D,hD,e,paid⟩ := boundedRows.{u} g hg periods strict h p S compact outside hC hB L R
  refine ⟨D,hD,e,?_⟩
  filter_upwards [paid] with w hw
  intro i x hx y hy u hu v hv
  obtain rfl : x = 0 := Set.mem_singleton_iff.mp hx
  exact (hw i y hy u hu v hv).1

end YM.FVA2.GradedFar.AppointedCenteredRounded
