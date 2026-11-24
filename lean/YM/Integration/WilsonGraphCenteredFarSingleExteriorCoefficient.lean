import YM.Integration.WilsonGraphCenteredFarBilinearCauchy

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedExteriorAtOrigin

open Function Filter Real PowerSeries Finset Continuation
open Register MS MS.Native MS.Land MS.Book MS.Book.Program
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Reg.Point
open scoped BigOperators Classical

variable {G : Gauge} (N : Register.WilsonPrescription G)

private theorem unitTax {h : ℕ} (u : Sec G h) (b : Dime G h) :
    tax (1 : Guard G h) u b = C ((dime G h).repr u b) := by
  refine PowerSeries.ext fun i => ?_
  simp only [tax, coeff_mk, coeff_one, coeff_C]
  split_ifs with hi
  · subst i; rfl
  · simp

private theorem single (h : ℕ) (A : Guard G h) (v : Sec G h) (b : Dime G h)
    (F : PowerSeries ℂ) (j : ℕ) :
    coeff j (tax A v b * F) = ∑ D ∈ tally j 1,
      (dime G h).repr ((coeff (D (some 0)) A) v) b * coeff (D none) F := by
  have q := Constants.admits (d := j) (fun _ : Fin 1 => tax A v b) F
  simpa only [Fin.prod_univ_one, tax, coeff_mk] using q

private theorem coordinates {h : ℕ} (F : XSpace.Structure1.Point G h 2) (u w : Sec G h) :
    F ![u,w] = ∑ c : Fin 2 → Dime G h,
      ((dime G h).repr u (c 0) * (dime G h).repr w (c 1)) * F (fun i => dime G h (c i)) := by
  have paid := F.map_sum (fun (i : Fin 2) (j : Dime G h) => (dime G h).repr (![u,w] i) j • dime G h j)
  simpa only [Module.Basis.sum_repr, F.map_smul_univ, smul_eq_mul, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one] using paid

/-- The single actual exterior contributes exactly one degree in the original one-slot tally. -/
theorem coefficient (h : ℕ) (x : Scale.Stage 2) (A : Guard G h) (u v : Sec G h) (j : ℕ) :
    coeff j (AppointedBilinearCauchy.full N h x 1 A u v) =
      ∑ D ∈ tally j 1, book N h 2 x (D none) ![u,(coeff (D (some 0)) A) v] := by
  unfold AppointedBilinearCauchy.full
  simp_rw [map_sum, unitTax, mul_assoc, coeff_C_mul, single, Finset.mul_sum, Reg.Point.story, coeff_mk]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D _
  rw [coordinates]
  apply Finset.sum_congr rfl
  intro c _
  ring

end YM.FVA2.GradedFar.AppointedExteriorAtOrigin
