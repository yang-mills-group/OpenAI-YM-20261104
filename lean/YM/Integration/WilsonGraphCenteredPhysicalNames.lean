import YM.Integration.WilsonGraphCenteredFarPhysicalPrice
import YM.GradedFar.Physical.Contours

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCenteredPhysicalNames

open Function Real Growth Continuation
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS MS.Book MS.Land Scale Register O O.Enh O.Score Dframe
open YangMills YM.Answer.ContinuumLimit YM.Integration YM.OPE YM.OPE.Orbits
open scoped Topology BigOperators Classical

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)

private abbrev pick := WilsonGraphPaperPublication.publicPick.{u} g hg
  (ElectedPublication.order periods strict)
private abbrev scheme := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev hierarchy := YangMills.hierarchy (g := g) (pick.{u} g hg periods strict).pupil.last
  (pick.{u} g hg periods strict).pupil.P
private abbrev frame := ElectedMeasurement.frame (pick.{u} g hg periods strict) (scheme g hg)
private abbrev physical := Elected.Hframe (scheme g hg) (pick.{u} g hg periods strict).pupil.last
  (pick.{u} g hg periods strict).pupil.J

/-- The published correlation appearing inside the centered discrepancy, at the two
birth radii and at the indicated separation radius. -/
abbrev filedScalar (h : ℕ) (r t f : ℝ) (a b : Sec g.core h)
    (phase : Option (hierarchy.{u} g hg periods strict).Character) (o : Spacetime)
    (y : YM.Points 1) : ℂ :=
  let x : YangMills.Points 2 := WithLp.toLp 2 ![0,y 0]
  (hierarchy.{u} g hg periods strict).correlation phase
    ![⟨h,frame.{u} g hg periods strict r h a⟩,⟨h,frame.{u} g hg periods strict t h b⟩]
    (WithLp.toLp 2 fun i => o + f • x.ofLp i)

private theorem booked (h : ℕ) (r t f : ℝ) (hf : 0 < f) (a b : Sec g.core h)
    (phase : Option (hierarchy.{u} g hg periods strict).Character) (o : Spacetime)
    (y : YM.Points 1) (hx : (WithLp.toLp 2 ![0,y 0] : YM.Points 2) ∈ YM.conf 2) :
    filedScalar.{u} g hg periods strict h r t f a b phase o y =
      whole (spectator (pick.{u} g hg periods strict).pupil.last phase)
        (Physical.atPos r o (0 : YM.Points 1))
        (Physical.here (physical.{u} g hg periods strict) r (d := fun _ : Fin 1 => h) (fun _ => a))
        (Physical.atPos f o y)
        (Physical.here (physical.{u} g hg periods strict) t (d := fun _ : Fin 1 => h) (fun _ => b)) := by
  let V := pick.{u} g hg periods strict
  let J := physical.{u} g hg periods strict
  let x : YM.Points 2 := WithLp.toLp 2 ![0,y 0]
  let sites : YM.Points 2 := WithLp.toLp 2 fun i => o + f • x.ofLp i
  let tags : Fin 2 → (hierarchy.{u} g hg periods strict).Tag :=
    ![⟨h,frame.{u} g hg periods strict r h a⟩,⟨h,frame.{u} g hg periods strict t h b⟩]
  let word := fun i : Fin 2 => quoteTag (S := V.pupil.S) (tags i)
  let e : Fin 1 ⊕ Fin 1 ≃ Fin 2 := finSumFinEquiv
  have separated : sites ∈ YM.conf 2 := ElectedMeasurement.centerSeparated hf o x hx
  have chart : beside (Physical.atPos r o (0 : YM.Points 1)) (Physical.atPos f o y) =
      sites.ofLp ∘ e := by
    funext i
    rcases i with i | i <;> fin_cases i
    · change o + r • (0 : Spacetime) = o + f • (0 : Spacetime)
      simp
    · rfl
  have labels : beside
      (names (Physical.here J r (d := fun _ : Fin 1 => h) (fun _ => a)))
      (names (Physical.here J t (d := fun _ : Fin 1 => h) (fun _ => b))) = word ∘ e := by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  rw [whole_observed,chart,labels,
    perm_observe (spectator V.pupil.last phase) (spectate V.pupil.last phase).laws.toSymmetric e word separated,
    named_fin (spectator V.pupil.last phase) (spectate V.pupil.last phase).laws.toSymmetric word separated]
  rfl

/-- Both filed labels were born at the near radius. Their two sites are the origin
and the single point at the coarse radius of this same window. -/
theorem allNear (h : ℕ) (w : Window) (hr : 0 < w.len) (a b : Sec g.core h)
    (phase : Option (hierarchy.{u} g hg periods strict).Character) (o : Spacetime)
    (y : YM.Points 1) (hx : (WithLp.toLp 2 ![0,y 0] : YM.Points 2) ∈ YM.conf 2) :
    filedScalar.{u} g hg periods strict h w.len w.len w.Coarse a b phase o y =
      Physical.Y0 (pick.{u} g hg periods strict).pupil.last (physical.{u} g hg periods strict)
        (fun _ : Fin 1 => h) (fun _ : Fin 1 => h) w (phase,o) (0 : YM.Points 1) y
        (fun _ => a) (fun _ => b) := by
  rw [Physical.Y0_value]
  exact booked.{u} g hg periods strict h w.len w.len w.Coarse (mul_pos hr (exp_pos w.2)) a b phase o y hx

/-- The center keeps its near birth, while the far field is born at the same coarse
radius used for its actual site. This is the centered reading in the original contours. -/
theorem mixed (h : ℕ) (w : Window) (hr : 0 < w.len) (a b : Sec g.core h)
    (phase : Option (hierarchy.{u} g hg periods strict).Character) (o : Spacetime)
    (y : YM.Points 1) (hx : (WithLp.toLp 2 ![0,y 0] : YM.Points 2) ∈ YM.conf 2) :
    filedScalar.{u} g hg periods strict h w.len w.Coarse w.Coarse a b phase o y =
      Physical.Dactual (pick.{u} g hg periods strict).pupil.last (physical.{u} g hg periods strict)
        w.len w.Coarse (phase,o) y (e := fun _ : Fin 1 => h) (fun _ => b) a :=
  booked.{u} g hg periods strict h w.len w.Coarse w.Coarse (mul_pos hr (exp_pos w.2)) a b phase o y hx

end YM.FVA2.GradedFar.AppointedCenteredPhysicalNames

