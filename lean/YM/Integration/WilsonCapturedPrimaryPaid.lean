import YM.Integration.WilsonCapturedPrimaryEstimate

/-! A cutoff-independent loss for return of a positive-horizon signed primary.
The derivative order and the polynomial losses of the original rough wallet
are chosen before the coupling grade wanted from the received history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPaid
open Finset Function Set Labels Lattice Wilson RG Source Push.Local
open Next.Foundations ProjectorNext.Equivariance Trace.Physical.Germ
open WilsonCapturedPrimaryReading WilsonCapturedPrimaryCollar WilsonCapturedPrimaryEstimate
open WilsonFirstReceivedRadialStencil
open scoped Classical ContDiff

def gap (P v : ℕ) := P+v+1
def grade (P d v : ℕ) := P+d*gap P v

private theorem pay {g C : ℝ} (hg : 0<g) (h1 : g≤1) (hc : 0≤C) {k d : ℕ}
    (hk : k≤d) (P v : ℕ) :
    (C*g^grade P d v+C*g^grade P d v)/(g^gap P v)^k+
      (C/g^v)*g^gap P v ≤ (3*C)*g^P := by
  have lower : g^grade P d v ≤ g^P*(g^gap P v)^k := by
    rw [grade,pow_add,mul_comm d _,pow_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (pow_nonneg hg.le _)
      (pow_le_one₀ hg.le h1) hk) (pow_nonneg hg.le _)
  have left : (C*g^grade P d v+C*g^grade P d v)/(g^gap P v)^k ≤ (C+C)*g^P := by
    apply (div_le_iff₀ (pow_pos (pow_pos hg _) _)).2
    calc
      _ ≤ C*(g^P*(g^gap P v)^k)+C*(g^P*(g^gap P v)^k) :=
        add_le_add (mul_le_mul_of_nonneg_left lower hc) (mul_le_mul_of_nonneg_left lower hc)
      _ = _ := by ring
  have right : (C/g^v)*g^gap P v ≤ C*g^P := by
    rw [gap,pow_succ,pow_add]
    calc
      _ = (C*g^P)*g := by field_simp
      _ ≤ _ := mul_le_of_le_one_right (mul_nonneg hc (pow_nonneg hg.le _)) h1
  exact (add_le_add left right).trans_eq (by ring)

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}
variable {A : Hol G} {B : SectionData F} {o : Site n} {R : Rep G n}

/-- An individual nonconstant probe or the scalar probe on the funded row,
after its full signed healthy comparison. A support with an old forced
invoice uses precisely this same true remBound. -/
theorem probe (hb : B.Sound A) {q : Coefficient F n} (form : q.Format o A R) {κ s : ℝ}
    (paid : q.remBound o R κ s) (order : d ≤ R.p.order) (power : d ≤ R.p.power)
    (size : ∀ x∈B.stencil, ∀ i : Axis, 20*((x i).natAbs+1) ≤ n.val)
    (section_smooth : ∀ v, HasOrderAt (B.places v o) 1 d)
    {g C : ℝ} (hg : 0<g) (h1 : g≤1) (hc : 0≤C) (P v u : ℕ)
    (rent : s ≤ C/g^u) (p : Probe G d) (y : Polynomial ℂ) (D : ℕ)
    (degree : y.natDegree≤D) (rk : p.2.val≤D) :
    let Q := grade P d v
    let K := cutoff R.p g (Q+u)
    let t := g^gap P v
    let W := ray A R.p o K p
    (∀ x∈B.footprint o, separation x o ≤ radius R.p K) →
    (∀ z∈Icc 0 t, ContDiffAt ℝ (p.2.val+1) (reading B R o (kept q R.p K) ∘ W) z) →
    (∀ z∈Icc 0 t, ‖iteratedDeriv (p.2.val+1) (reading B R o (kept q R.p K) ∘ W) z‖ ≤ C/g^v) →
    (∀ j≤D, flags R.p.threshold (W (t*node D j))=∅) →
    (∀ j≤D, ‖reading B R o q (W (t*node D j))-y.eval ((t*node D j:ℝ):ℂ)‖ ≤ C*g^Q) →
    ‖runProbe F p (projection F A R.p.threshold o q)-(p.2.val.factorial:ℂ)*y.coeff p.2.val‖ ≤
      (probeFee A p*C+WilsonCapturedPrimaryPolynomial.price D p.2.val*(3*C))*g^P := by
  intro Q K t W stencil smooth rough clear values
  have cut : Real.exp (-(R.p.supportExponent*K))*s ≤ C*g^Q := by
    calc
      _ ≤ Real.exp (-(R.p.supportExponent*K))*(C/g^u) :=
        mul_le_mul_of_nonneg_left rent (Real.exp_nonneg _)
      _ ≤ g^(Q+u)*(C/g^u) :=
        mul_le_mul_of_nonneg_right (cut_price R.p hg (Q+u)) (div_nonneg hc (pow_nonneg hg.le _))
      _ = _ := by rw [pow_add]; field_simp
  have ans := sampled hb form paid order power size section_smooth K stencil p y D degree rk
    (pow_pos hg (gap P v)) (div_nonneg hc (pow_nonneg hg.le _)) smooth rough clear values
  have cn : 0≤probeFee A p :=
    (test_bound A p.1 d p.2.val (Nat.le_of_lt_succ p.2.isLt)).choose_spec.1
  have small := pay hg h1 hc (Nat.le_of_lt_succ p.2.isLt) P v
  have mono : g^Q ≤ g^P := pow_le_pow_of_le_one hg.le h1 (Nat.le_add_right ..)
  calc
    _ ≤ _ := ans
    _ ≤ probeFee A p*(C*g^P) + WilsonCapturedPrimaryPolynomial.price D p.2.val*((3*C)*g^P) := by
      apply add_le_add
      · rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (cut.trans (mul_le_mul_of_nonneg_left mono hc)) cn
      · apply mul_le_mul_of_nonneg_left _ (WilsonCapturedPrimaryPolynomial.price_nonneg ..)
        apply le_trans _ small
        exact add_le_add (div_le_div_of_nonneg_right (add_le_add cut le_rfl)
          (pow_nonneg (pow_nonneg hg.le _) _)) le_rfl
    _ = _ := by ring

end YM.Integration.WilsonCapturedPrimaryPaid
