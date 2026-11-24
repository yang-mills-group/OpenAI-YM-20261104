import YM.Integration.WilsonOriginalPivotWardEuler
import YM.XSpace.VertexProducts

/-! The finite Wilson group product is multiplied on the chosen cotree before its vacuum division. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPivotWardProduct

open Lattice RG Wilson PertExtension PertExtension.Orb XSpace XSpace.Taylor
open scoped Classical BigOperators ContDiff

/-- Finite Taylor multiplication uses only finitely many derivatives in each output degree. -/
private theorem taylor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (basis : Module.Basis ι ℝ E) {f g : E → ℂ}
    (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0) :
    expandTaylor basis (f*g) = expandTaylor basis f * expandTaylor basis g := by
  have each {u : E → ℂ} (hu : ContDiffAt ℝ ∞ u 0) (k : ℕ) : ContDiffAt ℝ (k:WithTop ℕ∞) u 0 :=
    hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have line {u : E → ℂ} (hu : ContDiffAt ℝ ∞ u 0) (x : E) (k : ℕ) :
      ContDiffAt ℝ k (fun t : ℝ => u (t • x)) 0 := by
    let L := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) x
    exact ContDiffAt.comp (f:=L) 0 (show ContDiffAt ℝ k u (L 0) by rw [map_zero]; exact each hu k)
      L.contDiff.contDiffAt
  apply PowerSeries.ext
  intro n
  apply from_real basis
  intro x
  rw [line_coeff basis (f:=f*g) n x (each (hf.mul hg) n), PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Pi.mul_apply]
  rw [iteratedDeriv_fun_mul (line hf x n) (line hg x n), map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_mul, line_coeff basis _ x (each hf _), line_coeff basis _ x (each hg _),
    Nat.cast_choose _ (by simpa using hk)]
  field_simp [Nat.factorial_ne_zero]

variable {G : Gauge} {p : Period} (T : p.Tree)

theorem product {f g : Config G p.side → ℝ} (hf : PreTest f) (hg : PreTest g) :
    FVA2.BareOrb.stencil T (f*g) = FVA2.BareOrb.stencil T f * FVA2.BareOrb.stencil T g := by
  let cv (u : Config G p.side → ℝ) := Complex.ofRealCLM ∘ (u ∘ T.links)
  have smooth {u : Config G p.side → ℝ} (h : PreTest u) : ContDiffAt ℝ ∞ (cv u) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (FVA2.OrbGerm.tree T h)
  change expandTaylor (T.basis G) (cv (f*g)) = expandTaylor (T.basis G) (cv f) * expandTaylor (T.basis G) (cv g)
  rw [show cv (f*g) = cv f * cv g from funext fun _ => Complex.ofReal_mul .., taylor _ (smooth hf) (smooth hg)]

end YM.Integration.WilsonOriginalPivotWardProduct
