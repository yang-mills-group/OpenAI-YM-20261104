import YM.Integration.WilsonCapturedPrimaryDecoder

/-! Fixed field derivatives of the independently issued finite polynomial
are priced at a probing scale independent of perturbation order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPredictionPanel
open Finset Labels Lattice Source Push.Local Next.Foundations Wilson
open WilsonFirstReceivedRadialStencil WilsonCapturedPrimaryDecoder Set
open scoped Classical BigOperators
variable {G : Gauge} {d : ℕ} (F : Labels.Frame G d)

def fee (D : ℕ) : ℝ := (F.extra+1:ℕ)*‖decode F‖*∑ p∈tests F,WilsonCapturedPrimaryPolynomial.price D p.2.val

theorem priced (y : Probe G d → Polynomial ℂ) (D : ℕ) (hD : ∀p∈tests F,(y p).natDegree ≤ D)
    (rk : d ≤ D) {t E : ℝ} (ht : 0<t) (one : t ≤ 1) (ep : 0 ≤ E)
    (values : ∀p∈tests F, ∀j ≤ D, ‖(y p).eval ((t*node D j:ℝ):ℂ)‖ ≤ E) :
    F.coeffSize (F.core (forecast F y)) ≤ fee F D*(E/t^d) := by
  let M := ∑ p∈tests F,WilsonCapturedPrimaryPolynomial.price D p.2.val
  have pp : 0 ≤ M := sum_nonneg fun i _ => WilsonCapturedPrimaryPolynomial.price_nonneg D i.2.val
  have ee : 0 ≤ E/t^d := div_nonneg ep (pow_nonneg ht.le _)
  have reading (p : Probe G d) (hp : p∈tests F) :
      ‖(p.2.val.factorial:ℂ)*(y p).coeff p.2.val‖ ≤ M*(E/t^d) := by
    let k := p.2.val
    have bound := WilsonCapturedPrimaryPolynomial.recover (fun _ : ℝ => (0:ℂ)) (y p) D k
      (hD p hp) ((Nat.le_of_lt_succ p.2.isLt).trans rk)
      (t:=t) (E:=E) (M:=0) ht le_rfl (fun _ _ => contDiffAt_const)
      (fun _ _ => by simp) (fun j hj => by simpa only [zero_sub,norm_neg] using values p hp j hj)
    simp at bound
    have kmax : t^d ≤ t^k := pow_le_pow_of_le_one ht.le one (Nat.le_of_lt_succ p.2.isLt)
    have right := div_le_div_of_nonneg_left ep (pow_pos ht _) kmax
    have scale : WilsonCapturedPrimaryPolynomial.price D k ≤ M :=
      single_le_sum (s:=tests F) (f:=fun i : Probe G d => WilsonCapturedPrimaryPolynomial.price D i.2.val)
        (fun i _ => WilsonCapturedPrimaryPolynomial.price_nonneg D i.2.val) hp
    simpa only [norm_mul,Complex.norm_natCast] using bound.trans (mul_le_mul scale right (div_nonneg ep (pow_nonneg ht.le _)) pp)
  have input : ‖fun p : tests F => (p.val.2.val.factorial:ℂ)*(y p.val).coeff p.val.2.val‖ ≤ M*(E/t^d) :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg pp ee)).mpr fun p => reading p.val p.property
  have core : F.coeffSize (F.core (forecast F y)) ≤ F.coeffSize (forecast F y) := by
    unfold Labels.Frame.coeffSize
    refine sum_le_sum fun i _ => ?_
    by_cases h : i=0
    · simp [Labels.Frame.core,h]
    · simp [Labels.Frame.core,h]
  refine core.trans ((size_le_norm F _).trans ?_)
  have op := (decode F).le_opNorm (fun p : tests F => (p.val.2.val.factorial:ℂ)*(y p.val).coeff p.val.2.val)
  calc
    _ ≤ (F.extra+1:ℕ)*(‖decode F‖*(M*(E/t^d))) := mul_le_mul_of_nonneg_left
      (op.trans (mul_le_mul_of_nonneg_left input (norm_nonneg _))) (Nat.cast_nonneg _)
    _ = _ := by unfold fee;dsimp only [M];ring

end YM.Integration.WilsonCapturedPrimaryPredictionPanel
