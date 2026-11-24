import YM.Integration.WilsonPositionProgramNormalizedInversion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramSeriesRead
open Finset Lattice Wilson RG XSpace PhysicalNext.Repeat.Legato Precision
open WilsonPositionProgramInversionMaterial
open scoped BigOperators Classical ENNReal
variable {G : Gauge} (R : Run G) {I : Type} [Fintype I] [LinearOrder I]
    (p : XSpace.Period) (d : I → ℕ) (z : I → Cover) (T : p.Tree)
abbrev Cuts (q : ℕ) := ↥(Finset.HasAntidiagonal.antidiagonal q)
abbrev Terms (q : ℕ) := Axes R d × Cuts q

def weight (q : ℕ) (ζ : Axes R d → PowerSeries ℂ) (u : Terms R d q) : ℂ :=
  PowerSeries.coeff u.2.val.1 (ζ u.1)

def row (D : ChartRatio G) (q : ℕ) (u : Terms R d q) : ℂ :=
  PowerSeries.coeff u.2.val.2 (reported R p d z D u.1)

theorem original (D : ChartRatio G) (legal : LocalRatio D) (q : ℕ)
    (ζ : Axes R d → PowerSeries ℂ) :
    PowerSeries.coeff (q+ceiling R d) (XSpace.Bare.normalized T G (finite R p d z T ζ)) =
      ∑ u : Terms R d q, weight R d q ζ u * row R p d z D q u := by
  rw [WilsonPositionProgramInversionMaterial.original R p d z T D legal ζ,
    PowerSeries.coeff_X_pow_mul,map_sum,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [PowerSeries.coeff_mul]
  exact (Finset.sum_attach ..).symm

theorem paid {J : Type} [Fintype J] (a X Y : J → ℂ) (δ : ℝ≥0∞)
    (fee : ∑ u, ‖X u-Y u‖ₑ ≤ δ) :
    ‖(∑ u, a u * X u)-∑ u, a u * Y u‖ₑ ≤ δ * ∑ u, ‖a u‖ₑ := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  refine (enorm_sum_le ..).trans (le_trans ?_ (mul_le_mul_left fee _))
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro u _
  rw [enorm_mul,mul_comm]
  exact mul_le_mul_right (Finset.single_le_sum (fun b _ => zero_le (a:=‖a b‖ₑ)) (mem_univ u)) _

end YM.Integration.WilsonPositionProgramSeriesRead
end
