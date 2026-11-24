import YM.Integration.LocalFormalCoefficients
import YM.FormalOPE.RG10.Reclosure

/-!
# The local Wilson prescription, in RG10 format

Periodic, fixed finite step. Compute one RG10 `FlatFeed` and vertices from the
coarse field, the genuine action data, and `Colors`. These data do *not* use
`Fk` or any assumed comparison. We use the convention allowed in `Vertices` of
putting the chart Jacobian in V as log-Jacobian. We include precisely the same
Hessian inverse, mean shift, Haar, plant action, loop and any extra log packets
as in the datum. W is *input*, not an extra witness per requested order. The marker
argument is the exponential of a possibly mixed log-source (each with its own
valuation payment, using the given occurrence census), not necessarily just a
product of unrelated letters on subsets. A tag/tree is fixed for the entire
calculation. No sewing with another family's covariance, tag probabilities,
period convention or normalization.

Prove funded, numerator equality, full retained-field-dependent conditional
denominator equality (relative to the common factored leading scalar),
pre-log and logarithmic output equalities at every coupling grade. The bridge
is by **coefficient integrals** in the two definitions and exact algebra. These
equalities are true even just as coefficient rules on all Colors; to use with
the intended interpretation as Taylor-expanded interactions with the indicated
leading quadratic split and insertion powers one uses `Bulk.Well`. Numerical
Laplace and use with prescribed physical stencils, etc. are addressed separately.
Not a statement that infinite-volume bulk kernels, finite periodic and finite
inversion-quotient calculations give the same answer. Not a statement about a
terminal scalar/MS limit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSMatch
open Function MeasureTheory
open Comparison.RG02 FormalOPE FormalOPE.RG10
open Marker Multi RG Wilson Lattice Precision Tree Exterior Next.SectorChange
open scoped Topology ContDiff BigOperators Classical

namespace Conditional

section packing

variable {V : Type} [DecidableEq V] [Fintype V] (R : Census V)

-- The two packages use extensionally the same polarization; use a marker
-- relabeling morphism, instead of casts along Finset equalities.
private def fromOrder (r : ℕ) : Extra.Trajectories.Names (Order.Board R r) (Polar.budget R (Fin r)) where
  e := Function.Embedding.refl _
  visible s := by
    have h := s.property
    change _ ∈ Finset.filter (fun l : Finset (V ⊕ Fin r) => l.toLeft ∈ R.choices ∧ l.toRight ∈ (Order.indices r).choices) _ at h
    change _ ∈ Finset.filter _ _
    have hi : s.val.image (Function.Embedding.refl (V ⊕ Fin r)) = s.val := Finset.ext (by simp)
    rw [hi]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2.1⟩

lemma series_logWord {R : Census V} (A : Word R) (h : Word.boot A = 1) (r : ℕ) :
    Order.series R r (Word.logWord A) = Extra.Trajectories.connected (Order.series R r A) := by
  have he (B : Word R) : Order.series R r B =
      (fromOrder R r).restriction (Polar.certify (Fin r) B) := by
    apply Order.Join.both_parts; intro s t
    have ht : (fromOrder R r).share (Order.Join.pair s t)= Polar.pay s t.val := by
      apply Subtype.ext
      change ((Order.Join.pair s t).val.image (Function.Embedding.refl (V ⊕ Fin r))) = _
      rw [show (Order.Join.pair s t).val.image (Function.Embedding.refl (V ⊕ Fin r)) = (Order.Join.pair s t).val from Finset.ext (by simp)]
      rfl
    rw [Order.polarization, Order.part_restrict, ht, Polar.certify_present, Polar.present_pay]
  rw [he, he A, Word.consistent A h]
  exact (fromOrder R r).connected_restrict ((Polar.present_quiet A).trans h)

end packing

variable {V : Type} [DecidableEq V] {R : Census V}
    {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip}
    {P : PathData G} {O : ChartRatio G}
    (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices)
    (W : Bulk.Colors R G f) (x : fieldDir G c 1)

local notation "E" => (Key F G → ℝ)
local notation "μ" => Gaussian.cloud (K.covariance F t)
local notation "u" => Bulk.translated K F x
local notation "I" => Bulk.geometric K F t W

/-- One Gaussian, not a product of separately resampled choices for each mark. -/
def feed : RG10.FlatFeed Unit E where
  chance _ := 1
  chance_nonneg _ := zero_le_one
  chance_one := by simp
  base _ := μ
  density _ _ := 1
  density_nonneg _ := Filter.Eventually.of_forall (fun _ => zero_le_one)
  density_integrable _ := integrable_const _
  mass_pos _ := by simp

lemma mean (g : Unit × E → ℂ) : (feed K F t).mean g = ∫ v,g ((),v) ∂μ := by
  simp [feed, FlatFeed.mean]

/-- Exclude the completed quadratic and use the negative of each higher
action coefficient. Explicit order of series variable is g (budget not
built into the feed). -/
def vertices : RG10.Vertices (Unit × E) where
  V y := PowerSeries.map Complex.ofRealHom
    (PowerSeries.mk (Assembly.vacuumLetter I (u y.2)))
  J _ := 1
  V0 := by funext a; simp [row, Assembly.vacuumLetter]
  J0 := by funext a; simp [row]

/-- With matching Colors, the removed degree-zero term after exponent scale
extraction really is the quadratic price for this same RG10 feed (plus the
known coarse contribution). -/
lemma leading (hW : Bulk.Well W) (z : E) :
    Assembly.jet I 2 (u z) = Bulk.infrared S p P F t (K.b F) x +
      Gaussian.force (K.covariance F t) z / 2 :=
  Bulk.completed K F t W x z hW

open PertExtension.Series
private lemma exp_vertex (x' : Unit × E) : (vertices K F t W x).weight x' =
    PowerSeries.map Complex.ofRealHom
      (PowerSeries.mk (fun i => Radial.expsum (Radial.layers I) i i (u x'.2))) := by
  let L := PowerSeries.mk fun j => Radial.layers I j (u x'.2)
  let A := PowerSeries.map Complex.ofRealHom
  have hx : (vertices K F t W x).V x'= A L := by
    change A (PowerSeries.mk (Assembly.vacuumLetter _ _)) = _
    rw [funext (fun j => Assembly.vacuum_eq I (u x'.2) j)]
  have h (k j : ℕ) : PowerSeries.coeff j (L ^ k) =
      Zone.TaylorPow (Radial.layers I) k j (u x'.2) := by
    induction k generalizing j with
    | zero => simp [Zone.TaylorPow]
    | succ k ih => simp [pow_succ, PowerSeries.coeff_mul, Zone.TaylorPow, Zone.mul, ih, L]
  rw [Vertices.weight, hx, show (vertices K F t W x).J x' = 1 from rfl, mul_one]
  apply PowerSeries.ext; intro j
  simp only [expTaylor, PowerSeries.coeff_mk, PowerSeries.coeff_map, Complex.ofRealHom_eq_coe, Radial.expsum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← map_pow, show PowerSeries.coeff j (A (L^i)) = (↑(PowerSeries.coeff j (L^i)):ℂ) from PowerSeries.coeff_map .., h]
  push_cast
  rfl

/-- Independent log input. Include coupling orders after valuation compensation
(later assert interpretation on the model aperture for `Bulk.Well`). -/
def inputLog (a : Unit × E) : Word R :=
  Assembly.curve W.power (Bulk.markFn S F W) (u a.2)

lemma cares (a : Unit × E) (i : Hot R) (n : ℕ) :
    PowerSeries.coeff n (Word.see i.val (inputLog K F W x a)) =
      Assembly.jet (Bulk.markFn S F W i) (W.power i + n) (u a.2) := by
  rw [Word.unfold_see, inputLog, Assembly.curve, PowerSeries.coeff_mk]
  exact part_lit _ i

lemma inputLog_quiet (a : Unit × E) : Word.vac R (inputLog K F W x a) = 0 := by
  apply PowerSeries.ext; intro i
  rw [Word.vac_eq, Word.unfold_see, map_zero]
  exact Assembly.mark_curve_quiet W.power (Bulk.markFn S F W) _ _

variable [Fintype V]

def inputWord (a : Unit × E) : Word R := Word.expMark (inputLog K F W x a)
lemma input_quiet : Word.read R.quiet (inputWord K F W x) = 1 :=
  funext fun a => Word.vac_exp _ (inputLog_quiet K F W x a)

local notation "A₁" => inputWord K F W x
local notation "W₁" => vertices K F t W x
local notation "F₁" => feed K F t
local notation "Φ" => FlatFeed.totalize W₁ A₁

theorem priced (a : Unit × E) : Φ a = Assembly.expansions W.power (Bulk.markFn S F W) I (u a.2) := by
  have hx : Word.sing R.quiet ((W₁).weight a) = Assembly.realCurve R
      (fun n => Radial.expsum (Radial.layers I) n n (u a.2)) := by
    apply Word.observe_ext; intro s
    apply PowerSeries.ext; intro k
    rw [Word.see_sing, Word.unfold_see, Assembly.realCoeff, Assembly.beads]
    split
    · rw [exp_vertex, PowerSeries.coeff_map, PowerSeries.coeff_mk]; rfl
    · rw [map_zero]
  unfold FlatFeed.totalize
  rw [hx]
  rfl

lemma same_row (s : R.Mode) (n : ℕ) (z : E) :
    row n (Word.read s Φ) ((),z) = Assembly.rows
      (Assembly.expansions W.power (Bulk.markFn S F W) I) s n (u z) := by
  rw [row, Word.read, Function.comp_apply, Word.unfold_see, priced]
  rfl

lemma funded : (F₁).markedFunded W₁ A₁ := by
  rintro s n ⟨⟩
  change Integrable (fun y : E => (↑(1:ℝ):ℂ)*row n (Word.read s Φ) ((),y)) μ
  simp_rw [Complex.ofReal_one, one_mul, same_row]
  have hx := (Assembly.gather (Bulk.stage K F x) (Bulk.hinge F) W.power (Bulk.markFn S F W) I
    (K.covariance F t) (K.symm F t) (K.positive F t) s (Order.pick n n)).1
  rw [Order.picked n le_rfl] at hx
  exact hx

/-- Preserve the entire degree/marker board; no numerical evaluation. -/
theorem raw (r : ℕ) : Bulk.Fk K F t W x r = Order.series R r ((F₁).columns Φ) := by
  apply Order.Join.both_parts; intro s a
  rw [Bulk.table, Order.polarization, ← Word.unfold_see, FlatFeed.column_eq,
    FlatFeed.average_coeff, mean]
  simp_rw [same_row]

lemma denominator_full : Word.vac R ((F₁).columns Φ) = (F₁).den W₁ := by
  rw [Word.vac_eq, FlatFeed.column_eq, FlatFeed.totalize_read, input_quiet, mul_one]; rfl

theorem denominator (r : ℕ) : Order.denominator (Bulk.Fk K F t W x r) =
    Order.series R r (Word.sing R.quiet ((F₁).den W₁)) := by
  rw [raw, Order.denominator, Order.bottom_map]
  apply congr_arg (Order.series R r)
  apply Word.observe_ext; intro s
  apply PowerSeries.ext; intro k
  rw [Word.unfold_see, PowerSeries.coeff_map, Order.pure_marks,
    Word.see_sing, ← Word.unfold_see, ← Word.vac_eq, denominator_full]
  split <;> simp

lemma recover : Word.sing R.quiet ((F₁).den W₁) * (F₁).close W₁ A₁ = (F₁).columns Φ := by
  apply Word.observe_ext; intro s
  rw [Word.spike_mul, FlatFeed.close_part, FlatFeed.step_den, FlatFeed.column_eq,
    FlatFeed.totalize_read]

theorem ordinary (r : ℕ) : Order.ratio (Bulk.Fk K F t W x r) =
    Order.series R r ((F₁).close W₁ A₁) := by
  symm
  apply Order.ratio_unique (Bulk.fk_unit K F t W x r)
  rw [denominator, ← map_mul, recover, raw]

theorem log_vac (r : ℕ) : Order.logVac (Bulk.Fk K F t W x r) =
    Order.series R r (Word.logWord (Word.sing R.quiet ((F₁).den W₁))) := by
  rw [Order.logVac, denominator, series_logWord];
  rw [Word.boot, Word.vac_eq, Word.see_sing, if_pos rfl, FlatFeed.den0]

theorem connected (r : ℕ) : Order.logMarked (Bulk.Fk K F t W x r) =
    Order.series R r ((F₁).contraction W₁ A₁) := by
  have ht : Word.boot ((F₁).close W₁ A₁) = 1 := by
    rw [Word.boot, FlatFeed.preserve_one _ _ (input_quiet ..)]; simp
  rw [Order.logMarked, ordinary, FlatFeed.contraction, series_logWord _ ht]

end Conditional
end YM.Integration.MSMatch
