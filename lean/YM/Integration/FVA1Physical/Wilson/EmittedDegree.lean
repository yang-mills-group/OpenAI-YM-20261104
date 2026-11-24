import YM.Integration.FVA1Physical.Wilson.CoarseRows

/-! A uniform degree ceiling for the normalized mixed polynomial emitted on
the coarse lattice. This ceiling precedes tests, periods and tag histories. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Cacao MSbar.Mosaic MSbar.Rolling MSbar.Lis MSbar.Bakery.Film MSbar.Midpoint MSbar.Heath
open RGComparison.Core16.Spool RGComparison.Core16.Lumen YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology BigOperators
variable {G:Gauge} {ι:Type} [Fintype ι]

def emittedDegree (p:ℕ):= (p+1+p)*(p+1+p)+2

theorem emitted_field_degree (A:Issue G) (χ:ChartRatio G) (I:ι→Lamp G) (o:ι→Site A.f)
    (part:Bool) (p:ℕ) (kind:Kind A.T) (profile:Expanse A.T 1 (p+1+p)) {i:ℕ} (hi:i ≤ p) :
    (PowerSeries.coeff i (emittedRows A χ (jointFieldBank I A o part) p)).totalDegree ≤ emittedDegree p := by
  let d:=p+1+p
  have hd:1 ≤ d:=by dsimp only [d]; omega
  let src:=jointFieldBank I A o part
  have bank (j:ℕ)(hj:j ≤ d):(PowerSeries.coeff j src).totalDegree ≤ d:=by
    change (PowerSeries.coeff j (jointFieldBank I A o part)).totalDegree ≤ _
    rw [jointFieldBank,PowerSeries.coeff_mk]
    exact (MvPolynomial.totalDegree_rename_le ..).trans ((lampRow_degree I part _ j).trans hj)
  have slope:Expanse (barbed A.F A.v χ A.T) d d:=by
    constructor
    intro j hj
    have bound:=(MSbar.Parma.expanseB A.F A.v χ d A.T profile).profile j hj
    simp only [one_mul] at bound
    exact bound.trans (Nat.add_le_add_right (le_mul_of_one_le_left (Nat.zero_le _) hd) 2)
  have out:=outgoing_degree p d _ src (fullCov A) (Rolling.well A.F A.v χ A.T kind) slope bank i hi
  rw [emittedRows,PowerSeries.coeff_map]
  exact (Rolling.clearD ..).trans out

end YM.Integration.FVA1Physical.Wilson
