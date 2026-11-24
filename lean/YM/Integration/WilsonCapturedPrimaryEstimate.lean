import YM.Integration.WilsonCapturedPrimaryRays
import YM.Integration.WilsonCapturedPrimaryPolynomial
import YM.Push.LOCAL_SPLITTING.Comparison

/-! Return the full native Wilson coordinate after a signed value comparison on
its genuine healthy rays. The true truncation wallet and the independent
polynomial are compared only after the complete physical grouping. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryEstimate
open Function Filter Finset Set Labels Lattice Wilson RG Source Push.Local
open Next.Foundations ProjectorNext.Equivariance Trace.Physical.Germ
open WilsonCapturedPrimaryReading WilsonCapturedPrimaryCollar
open WilsonFirstReceivedRadialStencil
open scoped Classical ContDiff

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}
variable {A : Hol G} {B : SectionData F} {o : Site n} {R : Rep G n}

def ray (A : Hol G) (P : BudgetPoint) (o : Site n) (K : ℕ) (p : Probe G d) :
    ℝ → Config G n := WilsonCapturedPrimaryRays.field A P o (radius P K) p

def probeFee (A : Hol G) (p : Probe G d) :=
  (test_bound A p.1 d p.2.val (Nat.le_of_lt_succ p.2.isLt)).choose

/-- The measured input in this estimate is the quotient on the complete physical
source. No inequality is imposed on the individual signed regulars. -/
theorem sampled (hb : B.Sound A) {q : Coefficient F n} (form : q.Format o A R)
    {κ s : ℝ} (paid : q.remBound o R κ s) (order : d ≤ R.p.order) (power : d ≤ R.p.power)
    (size : ∀ x∈B.stencil, ∀ i : Axis, 20*((x i).natAbs+1) ≤ n.val)
    (section_smooth : ∀ v, HasOrderAt (B.places v o) 1 d)
    (K : ℕ) (stencil : ∀ x∈B.footprint o, separation x o ≤ radius R.p K) (p : Probe G d)
    (y : Polynomial ℂ) (D : ℕ) (degree : y.natDegree ≤ D) (hk : p.2.val ≤ D)
    {t a M : ℝ} (ht : 0<t) (hm : 0≤M)
    (smooth : ∀ u∈Icc 0 t, ContDiffAt ℝ (p.2.val+1)
      (reading B R o (kept q R.p K) ∘ ray A R.p o K p) u)
    (rough : ∀ u∈Icc 0 t, ‖iteratedDeriv (p.2.val+1)
      (reading B R o (kept q R.p K) ∘ ray A R.p o K p) u‖ ≤ M)
    (clear : ∀ j ≤ D, flags R.p.threshold (ray A R.p o K p (t*node D j)) = ∅)
    (values : ∀ j ≤ D, ‖reading B R o q (ray A R.p o K p (t*node D j)) -
      y.eval ((t*node D j:ℝ):ℂ)‖ ≤ a) :
    ‖runProbe F p (projection F A R.p.threshold o q) - (p.2.val.factorial:ℂ)*y.coeff p.2.val‖ ≤
      probeFee A p * Real.exp (-(R.p.supportExponent*K))*s +
      WilsonCapturedPrimaryPolynomial.price D p.2.val *
      ((Real.exp (-(R.p.supportExponent*K))*s+a)/t^p.2.val+M*t) := by
  let q' := kept q R.p K
  let f := reading B R o q' ∘ ray A R.p o K p
  have seen j (hj : j≤D) : ‖f (t*node D j)-y.eval ((t*node D j:ℝ):ℂ)‖ ≤
      Real.exp (-(R.p.supportExponent*K))*s+a := by
    let U := ray A R.p o K p (t*node D j)
    have tri := dist_triangle (reading B R o q' U) (reading B R o q U) (y.eval ((t*node D j:ℝ):ℂ))
    simp only [dist_eq_norm] at tri
    have cut := omitted hb paid K U (clear j hj)
    rw [norm_sub_rev] at cut
    exact tri.trans (add_le_add cut (values j hj))
  have numeric := WilsonCapturedPrimaryPolynomial.recover f y D p.2.val degree hk ht hm smooth rough seen
  have exactJet := WilsonCapturedPrimaryRays.probe hb form paid order power size section_smooth K stencil p
  change runProbe F p (projection F A R.p.threshold o q') = iteratedDeriv p.2.val f 0 at exactJet
  rw [←exactJet] at numeric
  have tri := dist_triangle (runProbe F p (projection F A R.p.threshold o q))
    (runProbe F p (projection F A R.p.threshold o q')) ((p.2.val.factorial:ℂ)*y.coeff p.2.val)
  simp only [dist_eq_norm] at tri
  exact tri.trans (add_le_add (coordinate form paid order power K p) numeric)

/-- The inverse price is that of the fixed original horizon frame. Both
coordinates use the same finite dual including the scalar probe. -/
theorem returned (q : Coefficient F n) (b : F.Coeff) (H : Probe G d → ℝ)
    (hp : ∀ p∈tests F, 0≤H p)
    (probes : ∀ p∈tests F, ‖runProbe F p (projection F A R.p.threshold o q)-runProbe F p b‖ ≤ H p) :
    F.coeffSize (projection F A R.p.threshold o q-b) ≤
      testPrice F * ∑ p∈tests F, H p := by
  apply (probe_budget F).choose_spec.choose_spec.2 _ _ (sum_nonneg hp)
  intro p hp'
  rw [map_sub]
  exact (probes p hp').trans (single_le_sum hp hp')

end YM.Integration.WilsonCapturedPrimaryEstimate
