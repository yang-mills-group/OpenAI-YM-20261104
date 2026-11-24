import YM.Integration.WilsonCapturedPrimaryOnRun
import YM.Integration.WilsonCapturedPrimaryTariff
import YM.Trace.Physicalv2.GermPrices

/-! Read the whole captured Wilson source once, after its signed grouping.
The independent polynomial is sampled on the genuine reporting gauges. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryTruePanel
open Function Filter Finset Lattice Wilson RG Source Labels Push.Local
open Next.Foundations Planned.AtomRegular ProjectorNext.Equivariance Trace.Physical.Germ
open PhysicalNext.Repeat.Legato Pert.Asymptotics Stationary Comparison.RG02
open WilsonCapturedPrimaryAngles WilsonCapturedPrimaryAperture WilsonCapturedPrimaryPotential
open WilsonCapturedPrimaryPaid WilsonCapturedPrimaryCollar WilsonCapturedPrimaryReading WilsonFirstReceivedRadialStencil
open scoped Classical BigOperators Topology
variable {G : Gauge} {d : ℕ} (F : Labels.Frame G d) (A : Hol G) (S : SectionData F)

theorem original (R : Run G) (simple : G.Simple) (T D : ℕ) (rk : d≤D) {N per i : ℕ} (live : i<N)
    (wrapped : (eventually_atTop.mp (Trace.Physical.GermGraph.cut_flat R.family simple 0)).choose ≤ i)
    (late : (eventually_atTop.mp (WilsonCapturedPrimaryOnRun.readouts R simple F A S T 0 1 le_rfl)).choose ≤ i)
    (P : RG.Rep G (R.family.side i per)) (point : P.p = R.family.path.levels.budget i)
    (support : 1≤P.p.supportExponent) (rank : d+1≤P.p.order)
    (o : Site (R.family.side i per)) (q : Coefficient F (R.family.side i per)) {w κ rough α : ℝ}
    (read : Readable A S P.p (R.family.side i per) w) (form : q.Format o A P) (rem : q.remBound o P κ rough)
    (α₀ : 0≤α) (y : Probe G d → Polynomial ℂ) (degree : ∀ p∈tests F,(y p).natDegree≤D) :
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
      ‖reading S P o q (Integral.sample g angle)-(y p).eval (z:ℂ)‖ ≤ α*g^high) →
    F.coeffSize (projection F A P.p.threshold o q-WilsonCapturedPrimaryDecoder.forecast F y) ≤
      2*(I*g^T)*(α+w*(F.coeffSize (F.core (WilsonCapturedPrimaryDecoder.forecast F y))+
        WilsonCapturedPrimaryCoreBill.wrapFee F A*rough)+rough) := by
  intro b g high rad I small nodes
  have gp : 0≤g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have cold : wraps P.p (R.family.side i per)≤1 := by
    rw [point]
    have cap := (eventually_atTop.mp (Trace.Physical.GermGraph.cut_flat R.family simple 0)).choose_spec i wrapped per
    simp at cap
    exact cap
  apply WilsonCapturedPrimaryCoreBill.paid F A form rem read.order read.power cold _ read.nonneg
    (mul_nonneg (WilsonCapturedPrimaryTariff.inverse F A D) (pow_nonneg gp _)) α₀ small
  intro C cash allowance
  have cc := α₀.trans cash
  have support' := point ▸ support
  have rank' := point ▸ rank
  have measured := (eventually_atTop.mp (WilsonCapturedPrimaryOnRun.readouts R simple F A S T 0 1 le_rfl)).choose_spec
    i late N per live support' rank' P point o q w κ rough C read form rem cc
    (by simpa only [pow_zero,div_one] using allowance) D rk y degree
  have taken : ∀ p∈tests F, ‖runProbe F p (projection F A P.p.threshold o q)-p.2.val.factorial*(y p).coeff p.2.val‖ ≤
      WilsonCapturedPrimaryOriginal.fieldFee A p D*C*g^T := by
    apply measured
    intro p hp j hj z u angle window inside good
    have within (e) : ‖Exterior.collect G angle e‖ ≤ |bound G b g 1| := by
      have here := inside e
      rw [one_mul] at here
      exact here
    exact (nodes p hp j hj window within good).trans
      (mul_le_mul_of_nonneg_right cash (pow_nonneg gp high))
  apply (WilsonCapturedPrimaryDecoder.returned F A D _ y (mul_nonneg cc (pow_nonneg gp T))
    (fun p hp => (taken p hp).trans_eq (mul_assoc ..))).trans_eq
  ring

end YM.Integration.WilsonCapturedPrimaryTruePanel
