import YM.RGComparison.Core16.Laplace

/-!
# Combining the fixed geometry expansions on the finite descent

Full vacuum density, same common prefactor cancelling in the conditional insertion; some offsets
`u` in *inverse squared coupling* (not assumed to come from perturbative reset unless stated).
Exhibit power `g^dim` of non-tree relative integration. Ordinary rows (then later connected).
-/
set_option autoImplicit false
noncomputable section

namespace YM.RGComparison.Core16.Descent
open Lattice RG Tree Wilson Precision Push.BetaTransport
open Function Filter MeasureTheory Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open PertExtension PertExtension.Series Tested Radial
variable {G : Gauge} {n c : Side} (P : ChartRatio G) (R : LocalRatio P)
    (d : Descent n c)

/-- Full-lattice conditional bare observable germ (no quotient other than the gauge redundancy of
interior sites of each tree; not the inversion regulator). Stencil realization addressed later. -/
structure Testable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (g : Config G n → X) : Prop where
  neat : Continuous g
  invariant : GaugeInvariant g
  smooth : ContDiffAt ℝ ∞ (g ∘ d.fine 1 ∘ d.tablePath) 0

lemma unit_test : Testable d (1 : Config G n → ℝ) := ⟨continuous_const, fun _ _ => rfl, contDiffAt_const⟩

variable (u : ℕ → ℝ) (g : Config G n → ℝ) (a : ℝ)

/-- Freeze offsets in **β**, not asserting the formal future all-order couplings are exact.
`a` = desired referenced `g` (weak coupling, std dev scale). -/
def offset (i : ℕ) : ℝ := a⁻¹^2 + u i

lemma account_offset (t : d.Tags) (V : Config G c) (x : Fields G d) :
    d.account (offset u a) t V x = a⁻¹^2 * d.action t V x + d.account u t V x := by
  induction d generalizing u with
  | nil => change (_ + _)*_ = _ * (1 * _) + _ * _; ring
  | @push m i S T d ih =>
    rw [account, action_push, account]
    simp_rw [show upβ (offset u a) = offset (upβ u) a from rfl, ih, offset]; ring

def resetTerms (t : d.Tags) (x : Fields G d) :=
    Real.exp (- d.account u t 1 x) * g (d.fine 1 x)

lemma power_eq (t : d.Tags) (x : Fields G d) :
    d.integrand (offset u a) t g 1 x = power t (d.resetTerms u g t) a x := by
  rw [integrand, account_offset, power, resetTerms, neg_add, Real.exp_add, div_eq_mul_inv, inv_pow]
  ring_nf

def generation := ∑ t : d.Tags, region t (d.resetTerms u g t) univ

/-- Independent finite volume conditional coefficient definition (subtract scalar prefab first).
It evaluates *Gaussian moments of explicitly specified full Taylor expansions*. `phase_jet` is
useful to make this calculation less tag-dependent. Not a derivative of a report.
-/
def bareRank := ∑ t : d.Tags, gaussianTerm P t (d.resetTerms u g t)

/-- Full normalized conditional. Finite lattice and unrenormalized. This reads bare unscaled
power-zero test `g`, shift external powers for physical applications when using G coordinates. -/
def ranking := divide (bareRank P d u g) (bareRank P d u 1)

local notation "D" => Module.finrank ℝ (Coordinates G d)
variable {d a g}
lemma prefactor_equation (h : d.OK G) (hg : GaugeInvariant g) (hi : Continuous g) (ha : 0 < a) :
    d.scalar G (offset u a) * a^D * generation d u g a = d.weighted (offset u a) g 1 := by
  rw [path_formula h (offset u a) hi hg]
  simp_rw [power_eq, generation, Finset.sum_apply, region, setIntegral_univ, ← Finset.mul_sum]
  rw [mul_assoc, ←mul_assoc (a^D), mul_inv_cancel₀ (pow_pos ha _).ne',one_mul]

lemma conditioned_eq (h : d.OK G) (hg : GaugeInvariant g) (hi : Continuous g) (ha : 0 < a) :
    d.conditioned (offset u a) g 1 = generation d u g a / generation (G := G) d u 1 a := by
  rw [← mul_div_mul_left (generation ..) (generation ..) (c := d.scalar G (offset u a)*a^D)
    (mul_pos (scalar_pos ..) (pow_pos ha _)).ne']
  rw [prefactor_equation u h hg hi ha,prefactor_equation (g := 1) u h (fun _ _ => rfl) continuous_const ha, weighted_unit,div_eq_mul_inv, mul_comm]; rfl

lemma reset_env (h : d.OK G) (hf : Continuous g) (t : d.Tags) : Envelope (d.resetTerms u g t) := by
  have hz : Continuous (fun x : Fields G d => g (d.fine 1 x)) := hf.comp
    ((fine_continuous d).comp (continuous_const.prodMk continuous_id))
  have hA := isCompact_univ.exists_bound_of_continuousOn hz.continuousOn
  have hg : Envelope (fun x : Fields G d => d.account u t 1 x) := ⟨(account_envelope h u t).meas.comp
    (measurable_const.prodMk measurable_id), (account_envelope h u t).cost.choose, fun x =>
      (account_envelope h u t).cost.choose_spec (1,x)⟩
  exact hg.neg.exp.mul ⟨hz.measurable,hA.choose,fun x => hA.choose_spec x (Set.mem_univ _)⟩

lemma reset_flat_value (h : d.OK G) (t : d.Tags) (g : Config G n → ℝ) : d.resetTerms u g t 1 = g 1 := by
  unfold resetTerms; rw [account_flat h, neg_zero, Real.exp_zero, fine_flat, one_mul]

include R
lemma bare_comparison (h : d.Room G) (H : d.Testable g) : Aspiration (generation d u g) (bareRank P d u g) := by
  refine Aspiration.sum _ _ _ (fun i _ => ?_)
  exact expands P R i _ h (reset_env u (room_ok d h) H.neat i)
    (((account_smooth (room_ok d h) i u).of_le le_top |>.neg.exp).mul H.smooth)

lemma pivot (h : d.Room G) : 0 < bareRank P d u 1 0 := by
  simp only [bareRank, Finset.sum_apply]
  exact Finset.sum_pos (fun i _ => normalization_pos P R i _ h (reset_flat_value u (room_ok d h) i _ |>.symm ▸ zero_lt_one)) Finset.univ_nonempty

theorem coefficient_formula (h : d.Room G) (H : d.Testable g) :
    Aspiration (fun a => d.conditioned (offset u a) g 1) (ranking P d u g) := by
  have hp := (bare_comparison P R u h H).quotient (bare_comparison P R u h (unit_test d)) (pivot P R u h).ne'
  intro k
  obtain ⟨C,hc,h⟩ := hp k
  refine ⟨C,hc,?_⟩
  filter_upwards [h, Tested.eventually_pos] with t ht h₁
  rw [Pi.sub_apply, conditioned_eq u (room_ok d ‹_›) H.invariant H.neat h₁]
  exact ht
end YM.RGComparison.Core16.Descent
