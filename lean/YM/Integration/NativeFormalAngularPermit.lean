import YM.Integration.NativeFormalPrescriptionAgreement

/-! The FVA2 angular identity on the physical basis gives the polynomial
covariance required by the moving regulator at every formal order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFormalAngularPermit

open Lattice Labels MS MS.Local.Physical MS.Land MS.Menus
open FVA2 FVA2.ColorCode

variable {G : Gauge}

theorem step (F : Frames G) (s : Signed) (d : ℕ) (i j : Glyph (wings G) d) :
    FVAAlt2.Home.stepR F (wings G) d s i j = shows F s.ortho d i j := rfl

theorem row (F : Frames G) (s : Signed) (d : ℕ) (i j : Plaid (wings G) d) :
    FVAAlt2.Convert.roster F (wings G) d s i j = fee F s.ortho d i j := rfl

/-- Evaluating the matrix identity for the physical rotation on one
basis coefficient gives equality of the corresponding marked payments. -/
theorem evaluated (V : Warehouse G) (P : Prescription (wings G))
    (H : Blaze.ExactSpin V P) (s : Signed) (d : ℕ) (i : Plaid (wings G) d)
    (j : Glyph (wings G) d) (x : ℝ) (n : ℕ) :
    (∑ k : Plaid (wings G) d, (fee V.F s.ortho d i k : ℂ) * oil (P.fees d k) j n x) =
    ∑ k : Glyph (wings G) d, oil (P.fees d i) k n x * showsC V.F s.ortho d k j := by
  classical
  let b := sameAxis V.F d
  have plain (a : Glyph (wings G) d → ℂ) :
      b.coord j (Blaze.factory (T := V) a) = a j := by
    simp [Blaze.factory, b, Module.Basis.coord_apply,
      Finsupp.single_apply, mul_ite]
  have turned (a : Glyph (wings G) d → ℂ) :
      b.coord j (spin V.F s.ortho d (Blaze.factory (T := V) a)) =
        ∑ k, a k * showsC V.F s.ortho d k j := by
    simp only [Blaze.factory, map_sum, map_smul, smul_eq_mul]
    rfl
  have he := congrArg (b.coord j) (H.legal s d i x n).symm
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_sum, map_smul, smul_eq_mul, plain, turned] at he
  convert he using 1
  congr 3

/-- Polynomial payments agree because their real evaluations agree for all
logarithmic coordinates. -/
theorem permit (V : Warehouse G) (P : Prescription (wings G))
    (H : Blaze.ExactSpin V P) (d : ℕ) : FVAAlt2.Convert.Permit V.F (P.fees d) := by
  classical
  intro s n
  apply Matrix.ext
  intro i j
  apply Polynomial.funext
  intro x
  apply Complex.ofReal_injective
  have he := evaluated V P H s d i j x n
  simpa only [Matrix.mul_apply, Matrix.map_apply, FVAAlt2.Convert.wage_mat, Matrix.of_apply,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Complex.ofReal_sum,
    Complex.ofReal_mul, step, row, held_real, oil] using he

end YM.Integration.NativeFormalAngularPermit
end
