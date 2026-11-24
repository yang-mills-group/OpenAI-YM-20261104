import YM.Integration.WilsonCapturedPrimaryTruePanel
import Mathlib.LinearAlgebra.Lagrange
import YM.Integration.WilsonCapturedPrimaryOnRun
import YM.Integration.WilsonCapturedPrimaryTariff
import YM.Trace.Physicalv2.GermPrices

/-! Read the whole captured Wilson source once, after its signed grouping.
The independent polynomial is sampled on the genuine reporting gauges. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimarySampledPanel
open Function Filter Finset Lattice Wilson RG Source Labels Push.Local
open Next.Foundations Planned.AtomRegular ProjectorNext.Equivariance Trace.Physical.Germ
open PhysicalNext.Repeat.Legato Pert.Asymptotics Stationary Comparison.RG02
open WilsonCapturedPrimaryAngles WilsonCapturedPrimaryAperture WilsonCapturedPrimaryPotential
open WilsonCapturedPrimaryPaid WilsonCapturedPrimaryCollar WilsonCapturedPrimaryReading WilsonFirstReceivedRadialStencil
open scoped Classical BigOperators Topology
variable {G : Gauge} {d : ℕ} (F : Labels.Frame G d) (A : Hol G) (S : SectionData F)

/-- Evaluate the independently supplied table on exactly the nodes used by the original
positive-horizon reader. Both the global scalar and all addressed channels enter. -/
def sample (D : ℕ) (t : ℝ) (values : ℕ→ℂ) : Polynomial ℂ :=
  Lagrange.interpolate (range (D+1)) (fun j=>((t*node D j:ℝ):ℂ)) values

private theorem separated (D : ℕ) {t:ℝ} (ht:t≠0) :
    Set.InjOn (fun j=>((t*node D j:ℝ):ℂ)) (range (D+1)) := by
  intro i _ j _ eq
  have e : node D i=node D j := mul_left_cancel₀ ht (Complex.ofReal_injective eq)
  exact_mod_cast (div_left_inj' (by positivity : (D+1:ℕ)≠(0:ℝ))).mp e

theorem degree (D : ℕ) {t : ℝ} (ht:t≠0) (values : ℕ→ℂ) :
    (sample D t values).natDegree≤D := by
  apply Polynomial.natDegree_le_of_degree_le
  simpa [sample] using (Lagrange.degree_interpolate_le (r:=values) (separated D ht))

theorem at_node (D : ℕ) {t : ℝ} (ht:t≠0) (values : ℕ→ℂ) {j : ℕ} (hj:j≤D) :
    (sample D t values).eval ((t*node D j:ℝ):ℂ)=values j :=
  Lagrange.eval_interpolate_at_node values (separated D ht) (mem_range.mpr (Nat.lt_succ_of_le hj))

/-- A booked exact polynomial table gives the same decoder at every positive rank. -/
theorem identifies (D : ℕ) {t:ℝ} (ht:t≠0) (P:Polynomial ℂ) (cap:P.natDegree≤D) :
    sample D t (fun j=>P.eval ((t*node D j:ℝ):ℂ))=P := by
  have small : P.degree < ((range (D+1)).card : WithBot ℕ) := P.degree_le_natDegree.trans_lt (by
    rw [card_range]
    exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le cap))
  exact (Lagrange.eq_interpolate (separated D ht) small).symm

theorem original (R : Run G) (simple : G.Simple) (T D : ℕ) (rk : d≤D) {N per i : ℕ} (live : i<N)
    (wrapped : (eventually_atTop.mp (Trace.Physical.GermGraph.cut_flat R.family simple 0)).choose ≤ i)
    (late : (eventually_atTop.mp (WilsonCapturedPrimaryOnRun.readouts R simple F A S T 0 1 le_rfl)).choose ≤ i)
    (P : RG.Rep G (R.family.side i per)) (point : P.p = R.family.path.levels.budget i)
    (support : 1≤P.p.supportExponent) (rank : d+1≤P.p.order)
    (o : Site (R.family.side i per)) (q : Coefficient F (R.family.side i per)) {w κ rough α : ℝ}
    (read : Readable A S P.p (R.family.side i per) w) (form : q.Format o A P) (rem : q.remBound o P κ rough)
    (α₀ : 0≤α) (values : Probe G d → ℕ→ℂ) :
    let b := R.family.path.levels.budget i
    let g := regulatorRun R.family N per (i+1)
    let high := grade T d 1
    let rad := radius b (cutoff b g high)
    let I := WilsonCapturedPrimaryDecoder.invoice F A D
    (I*g^T)*w≤1/2 →
    (∀ p∈tests F, ∀ j≤D,
      let z := (g^gap T 1)*node D j
      let u := lifted A b o rad p g z
      let angle := Stationary.arm G (R.family.side i per) 1 u
      |bound G b g 1| ≤ (b.B:ℝ)^2*b.threshold/g →
      (∀e,‖Exterior.collect G angle e‖ ≤ |bound G b g 1|) →
      flags P.p.threshold (Integral.sample g angle)=∅ →
      ‖reading S P o q (Integral.sample g angle)-values p j‖ ≤ α*g^high) →
    F.coeffSize (projection F A P.p.threshold o q-WilsonCapturedPrimaryDecoder.forecast F (fun p=>sample D (g^gap T 1) (values p))) ≤
      2*(I*g^T)*(α+w*(F.coeffSize (F.core (WilsonCapturedPrimaryDecoder.forecast F (fun p=>sample D (g^gap T 1) (values p))))+
        WilsonCapturedPrimaryCoreBill.wrapFee F A*rough)+rough) := by
  intro β g high rad I cash billed
  have gp : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live))
  have tpos : g^gap T 1≠0 := pow_ne_zero _ gp.ne'
  apply WilsonCapturedPrimaryTruePanel.original F A S R simple T D rk live wrapped late
      P point support rank o q read form rem α₀ (fun p=>sample D (g^gap T 1) (values p))
      (fun p _=>degree D tpos (values p)) cash
  intro p hp j hj z u angle w inside cold
  rw [at_node D tpos (values p) hj]
  exact billed p hp j hj w inside cold

end YM.Integration.WilsonCapturedPrimarySampledPanel
