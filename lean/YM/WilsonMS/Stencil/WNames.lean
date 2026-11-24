import YM.WilsonMS.Stencil.ColumnsW

/-!
# Expand the existing MS prescription on this input menu

We need original columns at their OWN horizon even if calling at a higher.
Implement calls concretely instead of keeping nested LitBook hypotheses. Here
we use the XSpace stencil based on arbitrary `Initialize`. Only mark adapter
changes: `score` will still use exact same MS `motto`. No changes to the
literal `PhysicalSum`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BMenu
open MS.Logarithm
open XSpace Function Filter Set Finset MeasureTheory
open MS MS.Local MS.Local.Physical MS.Plane MS.High MS.Book MS.Book.Convolve MS.Book.Program
open MS.Menus MS.Land MS.Koszul MS.Cylinder MS.Cylinder.Lab MS.Native MS.Native.Paint
  MS.Native.Wilsonian
open MS.Native.Studio MS.Lifting MS.Native.Sew MS.Native.Draft MS.Color MS.Swirl MS.Swirl.Near
open Lattice Corrected
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {d r : ℕ} (W : Initialize G) (p : Team)
local notation "B" => Ensure.deck G
variable (u : Glyph (Ensure.deck G) d)

def data0 (u : Glyph (Ensure.deck G) d) : Labels.Label G u.size :=
  ⟨Theater.ΕData B u, Theater.limitH ((Theater.filmBasic B u).2),
    ((Theater.cinema ..).mp (Theater.filmBasic B u)).2.1⟩

lemma dataHere : data0 u ∈ Labels.Grade (u.size, u.grade) :=
  (Labels.pure_grade ..).mpr ((Theater.filmBasic B u).2)

lemma realG : Labels.realBar (data0 u) = data0 u :=
  Subtype.ext (((Theater.cinema ..).mp (Theater.filmBasic B u)).2.2)

abbrev more :=
  Fin (u.size + 1) × Fin u.grade

def further (v : more u) :=
  exactPart (W.surveys u.size) (data0 u) v.1.val v.2.val

def atom (v : more u) :=
  Webs.symbol (W.surveys u.size) (further W u v).val
local notation "Φ" => Webs.Midpt.portfolio W

lemma holds (v : more u) : Aura (atom W u v) v.2.val :=
  Webs.esteem _ (piece_lit _ (data0 u) (realG u) _ _)

def vertices :=
  Book.levels u.grade ((Φ).stamp u.size u.grade u.2.2) +
    ∑ i : more u, Book.levels (i.2.val : ℕ) (atom W u i)

/-- Exact log-index position-independent physical mark before any `Menu` shifts. -/
def preambleW (x : ℝ) : T (Dot G Cover) :=
  wobble G p x (vertices W u)

lemma pre_expanded (x : ℝ) :
    preambleW W p u x =
      Glyph.preamble Φ p u x + ∑ i, wobble G p x (Book.levels (i.2.val : ℤ) (atom W u i)) := by
  rw [preambleW, vertices, map_add, map_sum]
  rfl

lemma pre_w (x : ℝ) (hc : G.Simple) : Weightless (Spectrum G) (style G p x) (preambleW W p u x) := by
  apply wob_weight
  unfold vertices
  let P := actB (Spectrum G) + blocks (Spectrum G) (core G)
  change P _ = 0
  rw [map_add, map_sum, show P _ = 0 from ((Φ).levels u.size u.grade _).closed hc, Finset.sum_eq_zero,
    zero_add]
  exact fun i _ => (holds W u i).closed hc

lemma pre_ticks (x : ℝ) (k : ℕ) : Tuned (preambleW W p u x k) 0 := by
  rw [pre_expanded, Pi.add_apply, Finset.sum_apply]
  refine (Glyph.pre_c _ _ _ _ _).add (Tune.sum _ (fun i _ => ?_))
  exact stood p x (fun j => TuneModel (holds W u i).phase (j + i.2.val)) k

lemma pre_leg (k : ℕ) (x : ℝ) : Limit (preambleW W p u x k).val (k + u.grade) := by
  rw [pre_expanded, Pi.add_apply, Finset.sum_apply]
  apply Limit.add (Glyph.pre_cost Φ p u x k)
  rw [sum_stack]
  apply Limit.sum _
  intro i _
  exact
    inducedLimit (F := Book.levels i.2.val _)
      (fun j hj =>
        Limit.up (Limit.mod _ (j + (i.2.val : ℤ)))
          (by
            have h : i.2.val < u.grade := i.2.isLt
            omega))
      k.le_refl

lemma pre_ready (k : ℕ) : Ready (fun x => preambleW W p u x k) := by
  simp_rw [pre_expanded, Pi.add_apply, Finset.sum_apply]
  apply Ready.add_point (Glyph.pre_ready Φ p u k) (value_sum _ fun i _ => ?_)
  exact
    brief p (M := fun _ => Book.levels (i.2.val : ℕ) _) (r := k) (q := k + i.2.val)
      (fun _ j hj => Limit.up (Limit.mod _ ((j : ℤ) + (i.2.val : ℤ))) (by omega))
      (fun _ => Ready.const _)

lemma pre_flag (x : ℝ) (k : ℕ) : Colorless (preambleW W p u x k) := by
  simp_rw [pre_expanded, Pi.add_apply, Finset.sum_apply]
  exact
    Colorless.add (Glyph.pre_lit Φ p u x k)
      (Colorless.csum _ fun i _ => induced p x (fun j => ColorMod (holds W u i).lit (j + i.2.val)) k)

lemma start (x : ℝ) : Fits (preambleW W p u x 0) u.read u.grade u.size false := by
  unfold Fits
  rw [pre_expanded, Pi.add_apply, Finset.sum_apply, map_add, map_add,
    add_eq_left.mpr (show mask _ _ = 0 from ?_)]
  exact Glyph.pre_floor Φ p u x
  rw [map_sum, map_sum]
  exact
    Finset.sum_eq_zero fun i _ =>
      maskOff
        (by
          have h : i.2.val < u.grade := i.2.isLt
          omega)
        (Tone.oneRank
          (inducedLimit (q := (i.2.val : ℕ)) (F := Book.levels i.2.val _) (r := 0)
            (fun j hj => Limit.up (Limit.mod _ (j + i.2.val)) (by omega)) (by omega)))

lemma changeScale (x : ℝ) : preambleW W p u x = car (Y p x) (preambleW W (Stripped p) u x) :=
  sWob ..
end YM.WilsonMS.BMenu
