import YM.Push.STATIONARY_UNIFORM.Array
import YM.Next.FOUNDATIONS.TestBounds
import YM.PCalc.Chart

/-! The one-parameter coarse-link chart used by the moving physical Haar
posterior is exactly an original left exponential flow. The derivative
bills therefore involve only the selected links, at every sampled field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionRay
open Lattice Wilson RG Precision Tree Exterior Push.Uniform
open scoped BigOperators

variable {G : Gauge} {c : Side}

def direction (g : ℝ) (z : Positions (Primary c G)) : Directions G c :=
  collect G (tint G _ (g • z))

theorem field (g t : ℝ) (z : Positions (Primary c G)) :
    represent (tint G _ (g • (t • z))) = increment 1 (t • direction g z) := by
  rw [smul_comm g t, map_smul]
  rfl

theorem derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Config G c → E) (g : ℝ) (z : Positions (Primary c G)) (q : ℕ) (t : ℝ) :
    iteratedDeriv q (fun x : ℝ => F (represent (tint G _ (g • (x • z))))) t =
      leftDerivs F (List.replicate q (direction g z)) (represent (tint G _ (g • (t • z)))) := by
  simp_rw [field]
  exact (Next.Foundations.leftDerivs_diag 1 (direction g z) F q t).symm

end YM.Integration.WilsonPosteriorProjectionRay

