import YM.RGComparison.Core16.Trajectory
import YM.Next.UV_STRESS.Ramp
import YM.Next.MULTISOURCE.Monomial
import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion

/-!
# Bridge on the complete marked density

Work in the existing commutative, squarefree marker algebra. Can restrict to any permitted census.
The marker output is not a product of pushed singletons. Don't confuse kernel `Tags`
(`Descent.Tags`) with these insertion variables.

`signal_identification` exposes pointwise equality adapted to the engineering `(a m)^d` budget
convention of `Overlay`. `Lane.Works` needs _separate_ proof (our equality needs only step and
first equations and doesn't construct `Works`). We identify also with the concrete smooth
`Extra.Trajectories.Insertions` for the case of their `Field` germs (including `Probes C`).
Use `weighted_integral` or `Overlay.Lane.from_`/`pays` (when their actual estimate hypotheses are
met) for normalization in the global Wilson expectation. Here we normalize also the
field-dependent **conditional** density and freeze the factorial convention. No locality of these
cumulants nor norm transfer away from the SAME `L.sites` is inferred.
-/
set_option autoImplicit false
noncomputable section

namespace YM.RGComparison.Core16
open Lattice RG Tree Wilson Marker Overlay Extra.Trajectories
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
open MeasureTheory Filter
variable {G : Gauge} {n c : Side} {ι : Type} [DecidableEq ι]

/-- Take the full product, no disconnected terms dropped; pre- any projection. -/
def fullProduct (O : ι → Config G n → ℂ) (s : Finset ι) (U : Config G n) := ∏ i ∈ s, O i U

namespace Descent
variable (d : Descent n c) (R : Census ι) (β : ℕ → ℝ) (O : ι → Config G n → ℂ)
variable (V : Config G c)

def marks (V : Config G c) : Poly R := Poly.inject fun s => d.weighted β (fullProduct O s.val) V

def moments (V : Config G c) : Poly R := Poly.inject fun s => d.conditioned β (fullProduct O s.val) V

lemma weighted_unit_C (h : d.OK G) : d.weighted (G := G) β (fun _ => (1 : ℂ)) =
    Complex.ofReal ∘ d.vacuum β := by
  have he := output_linear (X := ℝ) h β Complex.ofRealCLM (bare_integrable (β d.depth))
  change (Complex.ofReal ∘ d.vacuum β) = d.output β (Complex.ofReal ∘ bare (β d.depth)) at he
  rw [weighted, he]
  apply congrArg (d.output β)
  funext i
  simp only [Pi.smul_apply', Function.comp_apply, Complex.real_smul, mul_one]

lemma mark_part (s : R.Mode) : (d.marks R β O V).part s = d.weighted β (fullProduct O s.val) V := rfl

lemma moment_part (s : R.Mode) : (d.moments R β O V).part s = d.conditioned β (fullProduct O s.val) V := rfl

lemma quiet_mark (h : d.OK G) : (d.marks R β O V).part R.quiet = d.vacuum (G := G) β V := by
  rw [mark_part, show fullProduct O R.quiet.val = _ from
    (show fullProduct O R.quiet.val = fun _ => 1 from funext fun x => Finset.prod_empty), weighted_unit_C d β h]; rfl

lemma conditional_mark (s : R.Mode) : (d.moments R β O V).part s =
    (((d.vacuum β V : ℝ) : ℂ))⁻¹ * (d.marks R β O V).part s := by
  unfold moments marks; rw [← Complex.ofReal_inv]
  exact Complex.real_smul ..

lemma quiet_moment (h : d.OK G) : (d.moments R β O V).part R.quiet = 1 := by
  rw [conditional_mark, quiet_mark d R β O V h,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (positive β h V).ne')]

lemma marks_eq (h : d.OK G) : d.marks R β O V = (d.vacuum β V : ℂ) • d.moments R β O V := by
  ext x
  rw [Poly.part_smul, conditional_mark, ← mul_assoc, mul_inv_cancel₀
    (Complex.ofReal_ne_zero.mpr (positive β h V).ne'), one_mul]

/-- Restriction in the actual marked algebra. No horizon-dependent retuning. -/
theorem moments_restrict {ι' : Type} [DecidableEq ι'] {S : Census ι'}
    (u : Names R S) (g : ι' → Config G n → ℂ) : u.restriction (d.moments S β g V) =
    d.moments R β (fun i => g (u.e i)) V := by
  ext x
  change d.conditioned β (fullProduct g (u.share x).val) V = _
  rw [moment_part]
  congr 1; exact funext fun j => Finset.prod_image (f := fun i => g i j) u.e.injective.injOn

variable [Fintype ι]

/-- The true joint cumulants of the finite-volume conditional readings, not a sum of log's
in the patch branches. `pass` uses ordinary `1/i!`. -/
def cumulants : Poly R := connected (d.moments R β O V)

theorem moments_cumulants (h : d.OK G) : d.moments R β O V = Poly.pass (d.cumulants R β O V) :=
    (pass_connected (d.quiet_moment R β O V h)).symm

theorem cumulants_restrict (h : d.OK G) {ι' : Type} [Fintype ι'] [DecidableEq ι'] {S : Census ι'}
    (u : Names R S) (g : ι' → Config G n → ℂ) : u.restriction (d.cumulants S β g V) =
    d.cumulants R β (fun i => g (u.e i)) V := by
  rw [cumulants, u.connected_restrict (d.quiet_moment S β g V h), moments_restrict]; rfl

/-- Diagnostic of the source factorials; identity even WITH unit, clipped etc. later when testing
the output on transfer equations. `Fintype ι` spent here in forming the FULL product. -/
theorem marks_nil (U : Config G n) :
    (nil : Descent n n).marks R β O U = (bare (β 0) U : ℂ) •
      (∏ i : ι, (1 + Poly.send (R.fire i) (O i U))) := by
  ext s
  rw [mark_part, weighted, output_nil, Poly.part_smul, Multi.polynomial]
  exact Complex.real_smul ..
end Descent

section adapter
variable {m N p r : ℕ} {C : Family G} (Z : Slices C.path.levels p) {R : Census ι}

lemma fullProduct_cont {O : ι → Config G n → ℂ} (h : ∀ i, Continuous (O i)) (s : R.Mode) :
    Continuous (fullProduct O s.val) := continuous_finsetProd _ fun i _ => h i


/-- Test exact step and vacuum equations; pointwise implementation equality. -/
theorem mark_identification (O : ι → Config G (C.side N p) → ℂ)
    (hO : ∀ i, Continuous (O i)) (e : ι → ℕ) (s : R.Mode) (Y : ∀ i : ℕ, Config G (C.side i p) → ℂ)
    (start : ∀ U, Y N U = Ride.bump (C.S.a N) s e * (bare (C.beta N p) U : ℂ)*fullProduct O s.val U)
    (step : ∀ i, r ≤ i → i < N → Y i = Ride.bump (C.S.block i).val s e •
      (C.path.levels.clock.op i p).push (C.path.β N p (i+1)) (Y (i+1)))
    (hr : r ≤ m) (hm : m ≤ N) :
    Y m = Ride.bump (C.S.a m) s e • (fun x => ((traversal Z hm).marks R (line C.path p m N) O x).part s) := by
  change Y m = _ • (traversal Z hm).weighted (line C.path p m N) (fullProduct O s.val)
  induction hm using Nat.decreasingInduction with
  | self =>
    rw [traversal_self]
    funext U
    rw [start]
    unfold Descent.weighted
    rw [Descent.output_nil, Pi.smul_apply, smul_eq_mul, Pi.smul_apply', Complex.real_smul]
    exact mul_assoc ..
  | of_succ m hm ih =>
    rw [step m hr hm, ih (hr.trans (Nat.le_succ _)), weighted_step Z _ hm, StepData.push_smul _ _ _ _
      (weighted_integrable Z hm _ (fullProduct_cont hO s))]
    rw [smul_smul, ← Next.UVStress.bump_steps]

/-- The budgeted Lane, expressed as an equality of full functions with our canonical output.
Not just identification of their integrals. -/
theorem signal_identification [Fintype ι] (L : Lane C.path R N p) (h : L.Works r)
    (hc : ∀ i, Continuous (L.uses i)) (s : R.Mode) (hr : r ≤ m) (hm : m ≤ N) :
    L.signal m s = Ride.bump (C.S.a m) s L.load •
      (fun x => ((traversal Z hm).marks R (line C.path p m N) L.uses x).part s) :=
  mark_identification Z _ hc _ s (fun m => L.signal m s) (fun U => h.first s U) (fun i hi hN => h.step i hi hN s) hr hm

theorem smooth_identification (A : Insertions C.path ι N p) (s : R.Mode) (hm : m ≤ N) :
    A.total s m ∘ matrixField = Ride.bump (C.S.a m) s A.load •
      (fun x => ((traversal Z hm).marks R (line C.path p m N) A.uses x).part s) := by
  refine mark_identification Z A.uses (fun i => (A.smooth i).continuous.comp matrixField_cont) A.load s
    (fun m => A.total s m ∘ matrixField) ?_ ?_ (Nat.zero_le _) hm
  · intro U; rw [A.total_top]; exact A.source_eq ..
  intro i _ hi
  funext x
  rw [Function.comp_apply, A.total_step _ i hi, Pi.smul_apply, Insertions.step_push i (A.smooth_total s hi).continuous]
  rfl

-- compatibility with Extra.Trajectories factor (engineering weight) extends to logarithm by
-- `pass_connected` / uniqueness. Keep hypothesis uses at field probes.
theorem ratios_identification (h : C.Makes) (A : Insertions C.path ι N p) (s : R.Mode) (hm : m ≤ N) (V) :
    (A.ratios R m (matrixField V)).part s = Ride.bump (C.S.a m) s A.load *
      ((traversal Z hm).moments R (line C.path p m N) A.uses V).part s := by
  have he := congr_fun (Insertions.vac_eq (p := p) (N := N) h.wilson hm) V
  rw [← vacuum_eq Z h.wilson hm] at he
  simp only [Function.comp_apply] at he
  have hf := congr_fun (smooth_identification Z A s hm) V
  rw [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at hf
  rw [A.part_ratios, hf, he, Descent.conditional_mark, Complex.ofReal_inv]
  ring
end adapter
end YM.RGComparison.Core16
