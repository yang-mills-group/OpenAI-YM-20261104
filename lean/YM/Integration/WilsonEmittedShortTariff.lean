import YM.Integration.WilsonEmittedOriginalRoom
import YM.Integration.WilsonEmittedSparseRows

/-! The actual single short halo has a bounded cover and a logarithmic derivative tariff at every original period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedShortTariff
open Lattice Wilson RG QuadraticLocal Push Push.AbsoluteSums Push.AbsoluteSums.Animals
open Comparison.Density Comparison.Density.Mirrors
open scoped BigOperators
variable {n:Side}

theorem cover (B:BudgetPoint) (x:Site n) :
    coverNumber B.B (neighborhood (B.B+1) x) ≤ 5^4 :=
  (Corona.cover_mono (Corona.halo_mono (show B.B+1≤2*B.B by have h:=B.B_pos;omega)
    (Finset.Subset.refl _)) _).trans (Corona.tile x 2 B.B B.B_pos)

theorem tax (B:BudgetPoint) (x:Site n) {a:ℝ} (ha:a≤102) :
    Real.exp (a*(coverNumber B.B (neighborhood (B.B+1) x):ℝ)) ≤ Real.exp (102*(5^4:ℝ)) := by
  apply Real.exp_le_exp.mpr
  have h:(coverNumber B.B (neighborhood (B.B+1) x):ℝ)≤(5:ℝ)^4:=by exact_mod_cast cover B x
  exact mul_le_mul ha h (Nat.cast_nonneg _) (by norm_num)

theorem focus (B:BudgetPoint) {H:ℝ} (hp:0≤Real.log H)
    (hb:B.B=Nat.ceil ((Real.log H)^2)) {k:ℕ} (h:k≤B.B) :
    Anchor.focus k 0 B^B.order ≤ 4^(B.power*B.order)*(1+Real.log H)^(2*B.power*B.order) := by
  have ceil:(B.B:ℝ)<(Real.log H)^2+1:=by rw [hb];exact Nat.ceil_lt_add_one (sq_nonneg _)
  have small:(k:ℝ)≤(B.B:ℝ):=by exact_mod_cast h
  have line:(1+(k:ℝ))≤ 4*(1+Real.log H)^2:=by nlinarith [sq_nonneg (Real.log H)]
  unfold Anchor.focus
  simp only [Nat.add_zero,←pow_mul]
  calc
    _ ≤ (4*(1+Real.log H)^2)^(B.power*B.order):=pow_le_pow_left₀ (by positivity) line _
    _ = (4:ℝ)^(B.power*B.order)*(1+Real.log H)^(2*B.power*B.order):=by
      rw [mul_pow,←pow_mul];simp only [Nat.mul_assoc]

end YM.Integration.WilsonEmittedShortTariff
end
