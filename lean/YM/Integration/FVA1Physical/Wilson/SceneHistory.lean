import YM.Integration.FVA1Physical.Wilson.SceneBridge
import YM.RGComparison.Core16.Trajectory

/-! A realized scene is the full Haar descent at its retuned couplings,
normalized at the identity of the retained torus. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson

open RG Lattice YM.Wilson Precision RGComparison.Core16
open MSbar MSbar.Rolling MSbar.Midpoint Comparison.RG02
open scoped Classical

variable {G : Gauge} {L : Levels G} {H : Horizon L} {O : ChartRatio G}
    {K : Kin H O} {N p k r : ℕ} {e : G.Color}

/-- Starting at the retained coupling, evaluate each displayed
coupling conversion along the same history, from coarse to fine. -/
def sceneCoupling (S : Scene L p r) : ℕ → ℕ → ℝ → ℝ
  | 0, _, g => g
  | n+1, m, g => sceneCoupling S n (m+1) (tiltMap (S.action m) r g)

def sceneTemperatures (S : Scene L p r) (m : ℕ) (g : ℝ) (i : ℕ) : ℝ :=
  Integral.temperature (sceneCoupling S i m g)

private theorem push_scale {c f : Side} (T : StepData c f) (b z : ℝ) (F : Config G f → ℝ) :
    T.push b (z • F) = z • T.push b F := by
  funext V
  simp only [StepData.push, Pi.smul_apply, smul_comm (_ : ℝ) z, MeasureTheory.integral_smul]

variable (S : Scene L p r) (hS : Realized K N p k r e S) (T : Slices L p) {m : ℕ}
include hS

/-- At all background fields, through every intervening scale, including
the full top Wilson law and each physical Haar kernel. All intermediate
normalizations cancel, irrespective of the forest slices. -/
theorem scene_descent (hm : m ≤ N) (hk : k ≤ m) (g : ℝ) :
    S.film m g = fun U => (traversal T hm).vacuum (sceneTemperatures S m g) U /
      (traversal T hm).vacuum (G:=G) (sceneTemperatures S m g) 1 := by
  induction hm using Nat.decreasingInduction generalizing g with
  | self =>
    funext U
    rw [traversal_self, hS.top0, breed, Descent.vacuum, Descent.output_nil]
    change bare (g⁻¹ ^ 2) U =
      bare (Integral.temperature g) U / bare (Integral.temperature g) (1 : Config G (L.S.side N p))
    rw [show bare (Integral.temperature g) (1 : Config G (L.S.side N p)) = 1 by
      rw [bare,pinPose,mul_zero,Real.exp_zero], div_one]
    exact congrArg (fun b : ℝ => bare b U) (inv_pow g 2)
  | of_succ m hm ih =>
    let t := tiltMap (S.action m) r g
    let β := sceneTemperatures S (m+1) t
    let W := (traversal T hm).vacuum (G:=G) β
    let B := L.clock.op m p
    have hW : 0 < W 1 := Descent.positive β (traversal_ok T hm) 1
    have raw (U : Config G (L.S.side m p)) :
        (traversal T hm.le).vacuum (sceneTemperatures S m g) U = B.push (Integral.temperature t) W U := by
      rw [traversal_push T hm]
      rfl
    have prior : S.film (m+1) t = (W 1)⁻¹ • W := by
      funext U
      simpa only [Pi.smul_apply,smul_eq_mul,div_eq_inv_mul] using congrFun (ih (by omega) t) U
    obtain ⟨_,_,_,eqn,_⟩ := hS.step m hm hk
    funext U
    rw [eqn]
    change shunt B (S.film (m+1)) t U = _
    rw [shunt_is_physical,raw U,raw 1,prior,push_scale]
    simp only [Pi.smul_apply,smul_eq_mul]
    exact mul_div_mul_left _ _ (inv_ne_zero hW.ne')

/-- The complete weak-coupling expansion of the explicitly retuned,
normalized Wilson history on the nonflat coarse chart. The inherited
expansion includes the same large-field and moving-window controls. -/
theorem scene_descent_trend (hm : m ≤ N) (hk : k ≤ m) :
    Trend (fun g U => (traversal T hm).vacuum (sceneTemperatures S m g) U /
        (traversal T hm).vacuum (G:=G) (sceneTemperatures S m g) 1)
      (S.Poly m) (K.path N m) (L.params m).clip r := by
  have eqn := funext (scene_descent S hS T hm hk)
  rw [← eqn]
  exact (hS.budget m hm hk).1

end YM.Integration.FVA1Physical.Wilson
