import YM.Integration.WilsonCapturedPrimaryOriginal

/-! Recover the full finite Wilson primary in its original scaled basis from
the prices on the fixed field probes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPanel
open Function Filter Finset Set Labels Lattice Wilson RG Source Push.Local
open Next.Foundations ProjectorNext.Equivariance Trace.Physical.Germ
open WilsonCapturedPrimaryReading WilsonCapturedPrimaryCollar WilsonCapturedPrimaryEstimate
open WilsonCapturedPrimaryAngles WilsonCapturedPrimaryAperture WilsonCapturedPrimaryPaid
open WilsonCapturedPrimaryOriginal WilsonFirstReceivedRadialStencil
open scoped Classical
variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}
variable {A : Hol G} {B : SectionData F} {o : Site n} {R : Rep G n}

def invoice (F : Labels.Frame G d) (A : Hol G) (D : ℕ) :=
  testPrice F * ∑ p∈tests F,fieldFee A p D

theorem fee_nonneg (A : Hol G) (p : Probe G d) (D : ℕ) : 0≤fieldFee A p D := by
  exact add_nonneg (test_bound A p.1 d p.2.val (Nat.le_of_lt_succ p.2.isLt)).choose_spec.1
    (mul_nonneg (by norm_num) (WilsonCapturedPrimaryPolynomial.price_nonneg ..))

/-- The finite inverse is the one of the original enrolled horizon. It
includes the identity-field reading alongside the positive derivatives. -/
theorem original {w : ℝ} (read : Readable A B R.p n w) {q : Coefficient F n}
    (form : q.Format o A R) {κ s : ℝ} (paid : q.remBound o R κ s)
    (extra : d+1≤R.p.order) {g C : ℝ} (hg : 0<g) (h1 : g≤1) (hc : 0≤C)
    (P v u : ℕ) (rent : s≤C/g^u) (b : F.Coeff) (D : ℕ) (rk : d≤D)
    (y : Probe G d → Polynomial ℂ) (deg : ∀ p∈tests F, (y p).natDegree≤D)
    (filed : ∀ p∈tests F, runProbe F p b=p.2.val.factorial*(y p).coeff p.2.val) :
    let Q := grade P d v
    let K := cutoff R.p g (Q+u)
    let r := radius R.p K
    let t := g^gap P v
    (∀ x∈B.footprint o, separation x o≤r) → R.p.threshold*(1+(r:ℝ))^2≤1 → 2*t≤1 →
    (∀ p∈tests F, 2*t*wallet A p r ≤ aperture G*R.p.threshold) →
    (∀ p∈tests F, WilsonCapturedPrimaryRough.price G (p.2.val+1) (wallet A p r)*
      (w*F.coeffSize (F.core q.x)+s) ≤ C/g^v) →
    (∀ p∈tests F, ∀ j≤D, ‖reading B R o q (ray A R.p o K p (t*node D j))-
      (y p).eval (((t*node D j:ℝ):ℂ))‖ ≤ C*g^Q) →
    F.coeffSize (projection F A R.p.threshold o q-b) ≤ invoice F A D*C*g^P := by
  intro Q K r t stencil geometry room aperture gross values
  have per p (hp : p∈tests F) := WilsonCapturedPrimaryOriginal.original read form paid extra hg h1 hc
    P v u rent p (y p) D (deg p hp) ((Nat.le_of_lt_succ p.2.isLt).trans rk)
    stencil geometry room (aperture p hp) (gross p hp) (values p hp)
  have answer := returned (A:=A) (R:=R) (o:=o) q b (fun p=>fieldFee A p D*C*g^P)
    (fun p _ => mul_nonneg (mul_nonneg (fee_nonneg ..) hc) (pow_nonneg hg.le _))
    (fun p hp => by rw [filed p hp];exact per p hp)
  exact answer.trans_eq (by unfold invoice;rw [←sum_mul,←sum_mul];ring)

end YM.Integration.WilsonCapturedPrimaryPanel
