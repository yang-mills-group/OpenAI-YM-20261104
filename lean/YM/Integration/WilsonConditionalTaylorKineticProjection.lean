import YM.MSbar.Chord.Locks
import YM.FVA2.Harvest

/-! The authentic finite torus kinetic functional detects exactly two
spatial field legs in each coupling row of the actual scalar reset. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorKineticProjection

open PowerSeries Function Finset Lattice RG Wilson Precision Push.Uniform Exterior MSbar MSbar.Rolling
open MSbar.Midpoint MSbar.Bakery MSbar.Bakery.Portal MSbar.Wave MvPolynomial
open MSbar.Cacao
open Work.F03 PertExtension.Series.Radial
open scoped Classical ContDiff BigOperators

variable {G : Gauge} {c : Side} (v : G.Color) (P : Pot (Primary c G))

private theorem radial {σ : Type} [Fintype σ] (A : MvPolynomial σ ℝ) {d : ℕ} (different : d≠2)
    (x : σ→ℝ) : jet (fun t : σ→ℝ=>MvPolynomial.eval t (homogeneousComponent d A)) 2 x=0 := by
  let f:=fun t : σ→ℝ=>MvPolynomial.eval t (homogeneousComponent d A)
  have smooth : ContDiff ℝ ω f:=Cacao.vent _
  have scale (t : ℝ) : f (t•x)=t^d * f x := Wave.hene (σ:=σ) t t x d A
  change jet f 2 x=0
  rw [homogeneous_derivative f x 2 (smooth.contDiffAt.of_le le_top),funext scale,
    iteratedDeriv_mul_const_field,iteratedDeriv_fun_pow_zero]
  simp [Ne.symm different]

theorem other {d : ℕ} (different : d≠2) : caliper c v (homogeneousComponent d P)=0 := by
  let f:=fun t : Positions (Primary c G)=>MvPolynomial.eval t (homogeneousComponent d P)
  have smooth : ContDiff ℝ ω f:=vent _
  have diag (x : Positions (Primary c G)) : iteratedFDeriv ℝ 2 f 0 ![x,x]=0 := by
    have hx:=radial P different x
    change ((2:ℕ).factorial:ℝ)⁻¹ * iteratedFDeriv ℝ 2 f 0 (fun _=>x)=0 at hx
    rw [show (fun _ : Fin 2=>x) = ![x,x] from by funext i; fin_cases i <;> rfl] at hx
    exact (mul_eq_zero.mp hx).resolve_left (by positivity)
  have zero : stackP c G (homogeneousComponent d P)=0 := by
    ext1 x; ext1 y
    change (fderiv ℝ (fderiv ℝ f) 0 x) y=0
    exact (iteratedFDeriv_two_apply f 0 ![x,y]).symm.trans
      (hessian_polar (Q:=fun _ _=>0) (smooth.contDiffAt.of_le le_top) (by simp) (by simp) diag x y)
  change stackH c v (stackP c G (homogeneousComponent d P))=0
  rw [zero,map_zero]

theorem two : caliper c v (homogeneousComponent 2 P)=caliper c v P := by
  let z:=caliper c v
  let M:=P.totalDegree+2
  have same:=congrArg z (Wave.buys M P (by dsimp [M]; omega))
  rw [map_sum] at same
  rw [←same,Finset.sum_eq_single_of_mem 2 (Finset.mem_range.mpr (by dsimp [M];omega))]
  intro d _ ne; exact other v P ne

theorem row (b : PowerSeries ℝ) (F : PowerSeries (Pot (Primary c G))) (i j : ℕ) :
    caliper c v (fare b F i j) = coeff j (b^2*(b⁻¹)^i) * caliper c v (coeff i F) := by
  unfold Wave.fare
  rw [map_sum,Finset.sum_eq_single_of_mem 2 (Finset.mem_range.mpr (by omega))]
  · rw [map_smul,two]; rfl
  intro d _ ne; rw [map_smul,other v (coeff i F) ne,smul_zero]

end YM.Integration.WilsonConditionalTaylorKineticProjection
end

