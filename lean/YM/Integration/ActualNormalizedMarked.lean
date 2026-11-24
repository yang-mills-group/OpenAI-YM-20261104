import YM.Integration.ActualNormalizedPush
import YM.Extra.MULTISOURCE_TRAJECTORIES.Initial

/-! Independent marked moments under the full conditional law of one actual
trajectory step. Literal log portraits enter the existing marked compiler.
Their product prices bound each normalized coefficient before taking the
supremum over independent tests and conditioning fields. This proves value
bounds; it does not provide a small local comparison remainder or its jets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open Lattice Wilson RG MeasureTheory Finset
open RemainderComparison RemainderComparison.Typeface
open Marker Extra.Trajectories PhysicalNext.Repeat.Lotus
open scoped BigOperators Classical

variable {G : Gauge} {ι : Type} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} {f : Side} {R : Rep G f}
    (M : ∀ i, Portrait R (E i)) (J : Marker.Census ι)

/-- Coefficients keep the exact legal selection, including overlapping sites. -/
def portraitInput (tests : ∀ i, E i) (U : Config G f) : Poly J :=
  Poly.inject fun q => ∏ i ∈ q.val, (((M i).angle (tests i)).ingredient U : ℂ)

theorem portraitInput_product (tests : ∀ i, E i) (U : Config G f) :
    portraitInput M J tests U = ∏ i, (1 +
      (((M i).angle (tests i)).ingredient U : ℂ) • Poly.send (J.fire i) 1) := by
  have h : portraitInput M J tests U =
      Poly.pass (∑ i, Poly.send (J.fire i)
        (((M i).angle (tests i)).ingredient U : ℂ)) :=
    by
      apply Marker.Poly.ext
      intro q
      exact (pass_fire (fun i => (((M i).angle (tests i)).ingredient U : ℂ)) q).symm
  rw [h, pass_sum _ _ (by simp [Census.fire])]
  apply Finset.prod_congr rfl
  intro i _
  apply congr_arg (1 + ·)
  apply Marker.Poly.ext
  intro q
  simp only [Poly.part_smul, Poly.part_send]
  split <;> simp

omit [Fintype ι] in
/-- The literal product bound is independent of the test choices. -/
theorem portraitInput_part_bound (tests : ∀ i, E i) (U : Config G f) (q : J.Mode) :
    ‖(portraitInput M J tests U).part q‖ ≤ ∏ i ∈ q.val, (M i).weight := by
  change ‖∏ i ∈ q.val, (((M i).angle (tests i)).ingredient U : ℂ)‖ ≤ _
  rw [norm_prod]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro i _
  rw [Complex.norm_real, Real.norm_eq_abs, ← (M i).budget (tests i)]
  exact ((M i).angle (tests i)).earn U

omit [Fintype ι] in
theorem portraitInput_part_measurable (tests : ∀ i, E i) (q : J.Mode) :
    Measurable (fun U => (portraitInput M J tests U).part q) := by
  change Measurable (fun U => ∏ i ∈ q.val,
    (((M i).angle (tests i)).ingredient U : ℂ))
  exact Finset.measurable_prod _ (fun i _ =>
    Complex.measurable_ofReal.comp ((M i).angle (tests i)).borel)

variable (C : Family G) {N p m : ℕ}
    (hC : C.Makes) (hm : m < N)
variable (M : ∀ i, Portrait (C.path.rep N p (m+1)) (E i))
include hC hm

/-- Each normalized coefficient is literally an actual conditional average. -/
def normalizedPortrait (tests : ∀ i, E i) (V : Config G (C.side m p)) : Poly J :=
  Poly.inject fun q => actualAverage C (N := N)
    (fun U => (portraitInput M J tests U).part q) V

omit [Fintype ι] in
theorem normalizedPortrait_bound (tests : ∀ i, E i)
    (V : Config G (C.side m p)) (q : J.Mode) :
    ‖(normalizedPortrait J C M tests V).part q‖ ≤ ∏ i ∈ q.val, (M i).weight :=
  actualAverage_norm_le C hC hm (fun U => portraitInput_part_bound M J tests U q) V

omit [Fintype ι] in
theorem normalizedPortrait_integrable (tests : ∀ i, E i)
    (V : Config G (C.side m p)) (q : J.Mode) :
    Integrable (fun U => actualConditionalDensity C N p m V U •
      (portraitInput M J tests U).part q) (prior G _) :=
  actualAverage_integrable C hC hm
    (portraitInput_part_measurable M J tests q).aestronglyMeasurable
    (fun U => portraitInput_part_bound M J tests U q) V

omit [Fintype ι] in
/-- The tests vary independently inside each coefficient norm, together with
all conditioning fields. The exact product price has no dimension factor. -/
theorem normalizedPortrait_envelope (base : ∀ i, E i) (q : J.Mode) :
    envelope (fun x : (∀ i, E i) × Config G (C.side m p) =>
      ‖(normalizedPortrait J C M x.1 x.2).part q‖) ≤
        ∏ i ∈ q.val, (M i).weight := by
  apply envelope_le
  · exact (norm_nonneg _).trans (portraitInput_part_bound M J base 1 q)
  intro x
  exact normalizedPortrait_bound J C hC hm M x.1 x.2 q

omit [Fintype ι] in
/-- The vacuum coefficient is exactly one on the actual step, at every field. -/
theorem normalizedPortrait_quiet (tests : ∀ i, E i)
    (V : Config G (C.side m p)) :
    (normalizedPortrait J C M tests V).part J.quiet = 1 := by
  change actualAverage C (N := N) (fun U => ∏ i ∈ J.quiet.val,
    (((M i).angle (tests i)).ingredient U : ℂ)) V = 1
  simp only [Census.quiet, Finset.prod_empty]
  exact actualAverage_const C hC hm (1 : ℂ) V

omit hC hm in
/-- An explicit equality of represented densities suffices for this integral
identity, without identifying the representations or changing the trajectory. -/
theorem actualAverage_marked_compiler
    (R' : Rep G (C.side (m+1) p))
    (M' : ∀ i, Portrait R' (E i))
    (hR : ∀ U, R'.eval U = (C.path.rep N p (m+1)).eval U)
    (slots : ι → ℕ) (hinj : Function.Injective slots)
    (hwing : ∀ i, (M' i).wing = Wing.logKey (slots i))
    (tests : ∀ i, E i) (V : Config G (C.side m p)) (q : J.Mode) :
    actualAverage C (N := N) (fun U => (portraitInput M' J tests U).part q) V =
      ((C.path.rep N p m).eval V)⁻¹ •
      (C.path.levels.clock.op m p).push (C.path.β N p (m+1))
        (fun U => (Serif.TuneR (brand (independentPortraits M') tests)
          Set.univ (fun _ => 1) 0 (fun i => Marker.Poly.send (J.fire i) 1)
          (C.path.levels.clock.op m p) U).part q) V := by
  have hd (U : Config G (C.side (m+1) p)) :
      (Serif.TuneR (brand (independentPortraits M') tests)
        Set.univ (fun _ => 1) 0 (fun i => Marker.Poly.send (J.fire i) 1)
        (C.path.levels.clock.op m p) U).part q =
      (C.path.rep N p (m+1)).eval U • (portraitInput M' J tests U).part q := by
    rw [log_portrait_marked_density R' (C.path.levels.clock.op m p)
      (independentPortraits M') tests slots hinj hwing J _ U]
    change (↑(R'.eval U) • ∏ i, (1 +
      (((M' i).angle (tests i)).ingredient U : ℂ) • Marker.Poly.send (J.fire i) 1)).part q = _
    rw [← portraitInput_product M' J tests U]
    change (R'.eval U : ℂ) * (portraitInput M' J tests U).part q = _
    rw [hR U]
    rfl
  simp_rw [hd]
  exact actualAverage_push C _ V

omit hC hm in
/-- The compiler identity specialized to the very same actual fine representation. -/
theorem normalizedPortrait_compiler (slots : ι → ℕ) (hinj : Function.Injective slots)
    (hwing : ∀ i, (M i).wing = Wing.logKey (slots i))
    (tests : ∀ i, E i) (V : Config G (C.side m p)) (q : J.Mode) :
    (normalizedPortrait J C M tests V).part q =
      ((C.path.rep N p m).eval V)⁻¹ •
      (C.path.levels.clock.op m p).push (C.path.β N p (m+1))
        (fun U => (Serif.TuneR (brand (independentPortraits M) tests)
          Set.univ (fun _ => 1) 0 (fun i => Marker.Poly.send (J.fire i) 1)
          (C.path.levels.clock.op m p) U).part q) V :=
  actualAverage_marked_compiler J C _ M (fun _ => rfl) slots hinj hwing tests V q

end YM.Integration
