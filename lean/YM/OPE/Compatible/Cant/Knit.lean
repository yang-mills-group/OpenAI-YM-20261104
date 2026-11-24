import YM.OPE.Compatible.Cant.Villa
import YM.OPE.Compatible.Cant.Qu
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.Jac
open Function Set Filter Hark PriceZ
open Drift
open scoped Topology BigOperators Classical
variable {M E F Q:Type}{u v:ℝ}{t p:M→ℝ}
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {g:E≃ₗ[ℝ] Jewel F}{S T:E→L[ℝ] E}
lemma Thruster.oars (X:Thruster g S T u)(p:E) : T (S p)= S (T p):=DFunLike.congr_fun (X.gauge.symm) p
lemma Thruster.win (X:Thruster g S T u)(U:Fin 3 →Dice E)(T':Ding U S)(h:∀ x y:E,Spice u T U x y=0)(hu:0 < u)(x y:E): U 1 ((T^1) x) ((T^1) y)=u*u*U 1 x y:=by rw [turbine1 X T', h]; simp only [pow_one,Nat.cast_one,mul_zero,add_zero]; exact hu
end YM.OPE.Quit.Jac
