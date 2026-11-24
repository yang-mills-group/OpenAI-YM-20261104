import YM.Integration.WilsonReceivedSourceCoefficientIncome
import YM.Integration.WilsonPositionProgramCurvedMarkedSlot

/-! The actual filed angular coefficient and its true forest jet on the common knot. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramFiledPrimitiveSalary
open Finset Function Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry QuadraticLocal.Sunrise
open Exterior Stationary Comparison.RG02 AllOrder AllOrder.Floe AllOrder.Floe.Step
open WilsonReceivedSourceCoefficientIncome
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {V X ι : Type} [DecidableEq V] {G : Gauge} {n : Side} {P : Passport n V} {Γ : Census V}

private theorem raised (a x:ℝ)(hx:0≤x):max 1 (a*x) ≤ max 1 a*(1+x):=by
  have ha:1≤ max 1 a:=le_max_left _ _
  have up:1≤1+x:=by linarith
  exact max_le (one_le_mul_of_one_le_of_one_le ha up) ((mul_le_mul_of_nonneg_right (le_max_right 1 a) hx).trans
    (mul_le_mul_of_nonneg_left (by linarith: x≤1+x) (zero_le_one.trans ha)))

theorem filed (M:ι→Row P Γ G X)(w:V→ℝ)(grades:V→ℕ){σ cost:ℝ}{order count shelf:ℕ}
    (estate:Scene.Armada M w grades σ cost order count shelf)(hs:0<σ)(x:X)
    (layout:Layout G)(tape:Finset Age)(s:Γ.Mode)(j:ℕ)(hj:j≤order)(u:fieldDir G n 1):
    let Y:=Air.craft M (fun v=>(M v).paint x) grades layout tape
    Poly.toll w s*‖(Air.discharge Y j u).part s‖ ≤
      (price G σ 1 order shelf*|(s.val.image P.origin).card*cost|)*(1+‖u‖)^(order+shelf+1) := by
  let a:Link G n:=(Stationary.arm G n 1).symm u
  have cq:∀e,‖collect G (Stationary.arm G n 1 a) e‖≤‖u‖:=by
    intro e
    rw [show Stationary.arm G n 1 a=u from (Stationary.arm G n 1).apply_symm_apply _]
    exact norm_le_pi_norm u (e.1,coord e.2)
  have sale:=WilsonReceivedSourceCoefficientIncome.original M w grades estate hs x a (norm_nonneg u) cq j hj
    layout tape s
  rw [show Stationary.arm G n 1 a=u from (Stationary.arm G n 1).apply_symm_apply _] at sale
  have purchased:price G σ ‖u‖ order shelf ≤ price G σ 1 order shelf*(1+‖u‖)^(order+shelf+1):=by
    unfold price
    simp only [mul_one]
    rw [←mul_pow]
    apply pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _))
    rw [show 2*(G.colorScale*‖u‖)/σ=(2*G.colorScale/σ)*‖u‖ by ring]
    exact raised _ _ (norm_nonneg u)
  apply sale.trans
  calc
    _ ≤ price G σ ‖u‖ order shelf*|(s.val.image P.origin).card*cost| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by unfold price;positivity)
    _ ≤ _:= (mul_le_mul_of_nonneg_right purchased (abs_nonneg _)).trans_eq (by ring)

end YM.Integration.WilsonPositionProgramFiledPrimitiveSalary
end
