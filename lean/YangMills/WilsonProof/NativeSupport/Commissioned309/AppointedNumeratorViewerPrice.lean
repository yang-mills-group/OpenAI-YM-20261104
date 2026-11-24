import YangMills.WilsonProof.NativeSupport.Commissioned309.AppointedPaidG6
import YangMills.WilsonProof.NativeSupport.Commissioned309.AppointedRadialCurrency
import YM.Integration.WilsonGraphCenteredFarWindowExpense
import YM.GradedFar.Round.Segment

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedNumeratorViewer
open Filter Function Real Set MeasureTheory PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window OPE Orbits Physical
open YangMills YM.Answer.ContinuumLimit YM.Integration
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {n m : ℕ} {A : Family G} {o : Extraction.Order} {P : Table A.book}

def farInput (H : FramesH P) {e : Fin m → ℕ} (w : Window)
    (v : Inputs G e) : Inputs G e :=
  fun j => (H w.Coarse (e j)).symm (H w.len (e j) (v j))

theorem originalAtFar (U : Spec.Final A o P) (H : FramesH P)
    {d : Fin n → ℕ} {e : Fin m → ℕ} (w : Window) (viewer : View U)
    (x : Points n) (y : Points m) (u : Inputs G d) (v : Inputs G e) :
    Physical.Y0 U H d e w viewer x y u v =
      Physical.Yactual U H w.len w.Coarse viewer x y u (farInput H w v) := by
  rw [Physical.Y0_value]
  unfold Physical.Yactual
  have same : Physical.here H w.Coarse (farInput H w v) = Physical.here H w.len v := by
    funext j
    exact (H w.Coarse (e j)).apply_symm_apply (H w.len (e j) (v j))
  rw [same]

theorem fromOwed (U : Spec.Final A o P) (Q : OPE.Orbits.Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (H : FramesH P) {d : Fin n → ℕ} {e : Fin m → ℕ} {k D r f : ℝ} {h : ℕ} {viewer : View U}
    {x : Points n} {y : Points m} {u : Inputs G d} {v : Inputs G e} {a : Sec G h}
    (paid : Physical.Owed U Q H k D h r f viewer x y u v a) :
    ‖Physical.Yactual U H r f viewer x y u v -
      Physical.Yactual U H r f (none,viewer.2) x y u v‖ ≤ D * (gYM G r)^(-k) * f := by
  refine le_trans ?_ paid.2.2
  exact (le_add_of_nonneg_right (norm_nonneg _)).trans
    (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _))

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev pick := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)
private abbrev Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev H := Elected.Hframe (Z g hg) (pick.{u} g hg periods strict).pupil.last (pick.{u} g hg periods strict).pupil.J

theorem onWindow {n : ℕ} (d : Fin n → ℕ) (h p : ℕ) {X : Set (YM.Points n)} {Y : Set (YM.Points 1)}
    (hX : IsCompact X) (hx : X ⊆ conf n) (hY : IsCompact Y) (hy : Y ⊆ Outside 1)
    (L R : ℝ) {C B : ℝ} (hC : 0<C) (hB : 0<B) :
    ∃ D : ℝ, 0<D ∧ ∀ᶠ w : Window in windows (upper g.core C B),
      ∀ viewer : View (pick.{u} g hg periods strict).pupil.last,
      ∀ x ∈ X, ∀ y ∈ Y, ∀ u : Inputs g.core d, Within L u →
      ∀ v : Inputs g.core (fun _ : Fin 1 => h), Within R v →
        ‖Physical.Y0 (pick.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
            d (fun _ : Fin 1 => h) w viewer x y u v -
          Physical.Y0 (pick.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
            d (fun _ : Fin 1 => h) w (none,viewer.2) x y u v‖ ≤ D * (meter g.core w.len)^(p+1) := by
  let simple := _root_.IssuedMaxwell.ElectedPrescription.simple g hg
  obtain ⟨k,D,hD,cost⟩ := (Appointed1860G6.paid.{u} g hg periods strict (d := d)
    (e := fun _ : Fin 1 => h) hX hx hY hy h L (2 * max R 0)).exists
  refine ⟨D*C,mul_pos hD hC,?_⟩
  have frames := (AppointedPhysicalWindowAndPhase.earned.{u} g hg periods strict).main 1 h hC hB
  have length := Physical.Round.spots_span (simple := simple) hC (B := B) (((p+1 : ℕ) : ℝ)+k)
  filter_upwards [cost C B hC hB, (windows_short _).eventually frames.2, windows_span _,
    (windows_separation _).eventually_ge_atTop (0:ℝ),length,(windows_short _).eventually (positive_g simple)]
    with w price bounds upper zero coarse hgauge
  intro viewer x member y outside u hu v hv
  let trans := AppointedCenteredReverse.transfer.{u} g hg periods strict h w.1 (Window.Coarse w)
  have back : ‖chairs g.core h trans‖ ≤ 2 := by
    change ‖chairs g.core h (AppointedCenteredReverse.transfer.{u} g hg periods strict h w.1 (w.1 * exp w.2))‖ ≤ 2
    rw [← (AppointedCenteredWindow.fields.{u} g hg periods strict h w.1 w.2).2]
    exact (bounds w.2 zero upper).2
  have hv' : Within (2 * max R 0) (farInput (H.{u} g hg periods strict) w v) := by
    intro j
    have start : Ball (max R 0) (v j) := fun b => (hv j b).trans (le_max_left _ _)
    have norm := (chair_ball (v j) (le_max_right R 0)).1 start
    change Ball (2*max R 0) (trans (v j))
    apply (chair_ball _ (by positivity)).2
    rw [← appointed]
    exact ((chairs g.core h trans).le_opNorm _).trans
      (mul_le_mul back norm (norm_nonneg _) (by norm_num))
  have paid := price viewer x member y outside u hu _ hv' (0 : Sec g.core h) (fun b => by simp)
  rw [originalAtFar,originalAtFar]
  have phase := fromOwed _ _ _ paid
  apply phase.trans
  calc
    D*(gYM g.core w.1)^(-k)*(Window.Coarse w) ≤
        D*(gYM g.core w.1)^(-k)*(C*(gYM g.core w.1)^(((p+1:ℕ):ℝ)+k)) :=
      mul_le_mul_of_nonneg_left coarse (by positivity)
    _ = (D*C)*(meter g.core w.1)^(p+1) := by
      have positive : 0 < gYM g.core w.1 := hgauge
      rw [AppointedRadialCurrency.price,Real.rpow_add positive,Real.rpow_neg positive.le,Real.rpow_natCast]
      field_simp

end YM.FVA2.GradedFar.AppointedNumeratorViewer

