import YM.Integration.WilsonOlderFreshPointCommission

/-! The zero-source-derivative axes give a single constant source test for the entire
native point-field frame. The detector reads its normalized cover column on the actual
selected digit trajectory. This includes its scalar coordinate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPointBasis
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations
open QuadraticLocal AllOrder.Ink
open scoped Classical BigOperators
variable {G : Gauge} {d D : ℕ}

def axis (F : Frame G d) (v : F.Index) : Letter F :=
  ⟨(v, ⟨0, (Dawn.paper_is 0).mpr (by simp [Chapel.upper])⟩),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [Chapel.upper] using F.bound v⟩⟩

def fixed (D : ℕ) : Studio D := Dawn.cone D 0

theorem same (F : Frame G d) (v : F.Index) : inside F (axis F v) D = fixed D := rfl

theorem axis_eq (F : Frame G d) (v w : F.Index) : axis F v = axis F w ↔ v = w :=
  ⟨congrArg (mint F), congrArg (axis F)⟩

def coordinate (F : Frame G d) (Z : Pot G) (v : F.Index) : Pence :=
  ∑ r∈range ((F.grades v).2+1),
    PowerSeries.mk (fun j=>pearlJ F (Z j r) v) * PowerSeries.X^((F.grades v).2-r)

def sample (F : Frame G d) (Z : Pot G) (p : ℕ) (θ g : ℝ) : F.Coeff :=
  fun v=>(((θ/g)^(F.grades v).2 * ∑e∈range (p+1),coeff e (coordinate F Z v)*g^e : ℝ) : ℂ)

theorem filed (F : Frame G d) (Y : Plaza F D) (o : Loc G 1) (normalized : Court o F Y)
    (row col : F.Index) :
    coordinate F (Y (axis F col) (fixed D)) row = if row=col then 1 else 0 := by
  have paid := normalized.city (axis F row) (axis F col)
  change coordinate F (Y (axis F col) (fixed D)) row =
    (if axis F row=axis F col then 1 else 0) at paid
  simpa only [axis_eq] using paid

theorem original (R : Run G) (L : Primer.Families R.family) (a : hue G) (depth : d<D)
    (i : ℕ) (t : WilsonPointChildFiledPress.Tour R i) (simple : G.Simple) (o : Loc G 1)
    (front : d≤R.family.path.levels.clock.J (i+1)) :
    let F := R.family.labels.level d
    let Z := fun v=>WilsonOlderFreshPointGauge.field R L a depth i (axis F v) (t,fixed D)
    ∀ row col : F.Index, coordinate F (Z col) row = (if row=col then 1 else 0) ∧
      ∀(p : ℕ)(θ g : ℝ), sample F (Z col) p θ g row =
        (((θ/g)^(F.grades row).2 : ℝ) : ℂ)*(if row=col then 1 else 0) := by
  intro F Z row col
  have paid := filed F _ o (WilsonNeutralPointCourse.original R L a depth t.digit
    t.cutoff i simple o t.live front) row col
  change coordinate F (Z col) row=(if row=col then 1 else 0) at paid
  refine ⟨paid,?_⟩
  intro p θ g
  simp only [sample,paid]
  by_cases h : row=col
  · simp [h,PowerSeries.coeff_one]
  · simp [h]

end YM.Integration.WilsonCapturedPrimaryPointBasis
