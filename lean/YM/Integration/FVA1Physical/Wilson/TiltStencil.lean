import YM.Integration.FVA1Physical.Wilson.WickStencil
import YM.MSbar.Cacao.Coda

/-! A finite marked formal interaction uses the full conditional vacuum.
Its normalized coefficient is a universal polynomial in the selected mean
and covariance, equal to the installed connected Wilson insertion. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open MeasureTheory Matrix MvPolynomial Finset MSbar.Cacao Further.GaussianScalar
open scoped Classical
variable {σ ι : Type} [Fintype σ] [DecidableEq σ]
def wickSeries (F : PowerSeries (Pot σ)) : PowerSeries (Pot (WickSlot σ)) :=
  PowerSeries.mk fun n=>wickStencil (PowerSeries.coeff n F)

def tiltedStencil (f F : PowerSeries (Pot σ)) : PowerSeries (Pot (WickSlot σ)) :=
  wickSeries (F*Spring f) * PowerSeries.invOfUnit (wickSeries (Spring f)) 1

omit [DecidableEq σ] in
lemma wickStencil_one : wickStencil (1:Pot σ)=1 := by
  simp [wickStencil,heatStencil]

omit [DecidableEq σ] in
lemma tiltedStencil_clear (f F : PowerSeries (Pot σ)) (hf : Kind f) :
    tiltedStencil f F * wickSeries (Spring f) = wickSeries (F*Spring f) := by
  unfold tiltedStencil
  rw [mul_assoc, PowerSeries.invOfUnit_mul, mul_one]
  rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply,wickSeries,PowerSeries.coeff_mk,covers hf,wickStencil_one]
  rfl

private lemma quotient_unique (a b v : PowerSeries ℝ) (hv : PowerSeries.coeff 0 v=1) (r : ℕ)
    (same : ∀ n, n<r → PowerSeries.coeff n (a*v)=PowerSeries.coeff n (b*v)) :
    ∀ n, n<r → PowerSeries.coeff n a=PowerSeries.coeff n b := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnr
    have eq:=same n hnr
    simp only [elevator,Finset.sum_range_succ,Nat.sub_self,hv,mul_one] at eq
    have head : ∑ j∈Finset.range n,PowerSeries.coeff j a*PowerSeries.coeff (n-j) v =
          ∑ j∈Finset.range n,PowerSeries.coeff j b*PowerSeries.coeff (n-j) v :=
      Finset.sum_congr rfl fun j hj=> by rw [ih j (mem_range.mp hj) ((mem_range.mp hj).trans hnr)]
    rw [head] at eq; exact add_left_cancel eq

theorem tiltedStencil_eq_grow [Fintype ι] [DecidableEq ι] (v : Matrix σ ι ℝ) (x : View σ)
    {C : Matrix ι ι ℝ} (hc : C.PosDef) (f F : PowerSeries (Pot σ)) (hf : Kind f)
    (r n : ℕ) (hn : n<r) :
    eval (parameters x (v*C*v.transpose)) (PowerSeries.coeff n (tiltedStencil f F)) =
    eval x (PowerSeries.coeff n (growP f F (v*C*v.transpose) r)) := by
  let u:=eval (parameters x (v*C*v.transpose))
  let a:=PowerSeries.map u (tiltedStencil f F)
  let w:=PowerSeries.map u (wickSeries (Spring f))
  let b:=PowerSeries.map (eval x) (growP f F (v*C*v.transpose) r)
  let q:=PowerSeries.map (eval x) (Spring (confect (v*C*v.transpose) f))
  have den : w=q := by
    apply PowerSeries.ext; intro i
    simp only [w,q,u,wickSeries,PowerSeries.coeff_map,PowerSeries.coeff_mk]
    exact (wickStencil_integral v x hc _).trans (goodie v x hc hf i).symm
  have hw : PowerSeries.coeff 0 w=1 :=by
    simp only [w,wickSeries,PowerSeries.coeff_map,PowerSeries.coeff_mk,covers hf,wickStencil_one,_root_.map_one]
  have paid (i : ℕ) (hi : i<r) : PowerSeries.coeff i (a*w)=PowerSeries.coeff i (b*w) := by
    change PowerSeries.coeff i (PowerSeries.map u (tiltedStencil f F) * PowerSeries.map u (wickSeries (Spring f))) =
      PowerSeries.coeff i (b*w)
    rw [←_root_.map_mul,tiltedStencil_clear f F hf,PowerSeries.coeff_map,wickSeries,
      PowerSeries.coeff_mk,den]
    change eval (parameters x (v*C*v.transpose)) _=PowerSeries.coeff i
      (PowerSeries.map (eval x) _ * PowerSeries.map (eval x) _)
    rw [←_root_.map_mul,PowerSeries.coeff_map]
    exact (wickStencil_integral v x hc _).trans (aromaEval v x hc f F hf hi).symm
  exact quotient_unique a b w hw r paid n hn

end YM.Integration.FVA1Physical.Wilson
