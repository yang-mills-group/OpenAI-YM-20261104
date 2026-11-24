import YM.Integration.WilsonPositionScaleLawGuardStock
import YM.Integration.WilsonPositionScaleLawGuardSheet

/-! Compact control of the complete finite overflow is reduced to the bounded
lower-order coefficients actually printed in the independent prescription. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardWindow
open Finset PowerSeries WilsonPositionScaleLawGuardStock
open WilsonPositionScaleLawGuardPoly (mass)
open WilsonPositionScaleLawGuardCancellation (fringe)
open WilsonPositionScaleLawGuardSubstitute (composed)
open scoped Polynomial Classical BigOperators
variable {I R:Type*}[NormedRing R][NormedAlgebra ℂ R]

theorem central {p:I→ℂ[X]}(s:Stock p):Stock (fun x=>(p x).map (algebraMap ℂ R)):=by
  obtain ⟨N,A,hA,paid⟩:=s
  refine ⟨N,A*‖(1:R)‖,mul_nonneg hA (norm_nonneg _),fun x=>⟨Polynomial.natDegree_map_le.trans (paid x).1,?_⟩⟩
  intro k;rw [Polynomial.coeff_map]
  have e:(algebraMap ℂ R) ((p x).coeff k)=(p x).coeff k • (1:R):=by rw [Algebra.smul_def,mul_one]
  rw [e,norm_smul]
  exact mul_le_mul_of_nonneg_right ((paid x).2 k) (norm_nonneg _)

theorem original (q:ℕ)(p:I→PowerSeries ℂ)(a:PowerSeries R)(c n b:I→PowerSeries R)
    (hp:Stock (fun x=>trunc (q+1) (p x)))(hc:Stock (fun x=>trunc (q+1) (c x)))
    (hn:Stock (fun x=>trunc (q+1) (n x)))(hb:Stock (fun x=>trunc (q+1) (b x))):
    ∃T:ℝ,0≤T ∧ ∀x,mass (fringe q (p x) a (c x) (n x) (b x))≤T:=by
  have made:Stock (fun x=>composed q (trunc (q+1) (p x)) a):=by
    apply many;intro j _
    exact times (central (R:=R) (powers hp j)) (fixed (I:=I) (Polynomial.C (coeff j a)))
  exact cost (minus (times hb made) (times hc hn))

end YM.Integration.WilsonPositionScaleLawGuardWindow
