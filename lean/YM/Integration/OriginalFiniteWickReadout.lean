import YM.Integration.PeriodicMarkedHeat
import YM.WilsonCoeffUV.Series.FormalWick
import YM.Comparison.RG02.Valence.Amplify

/-! Coarse-field evaluation of the native formal Wick series agrees with
the RG02 complex Gaussian coefficient on its original finite free keys. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalFiniteWickReadout
open Function Finset MvPolynomial WilsonCoeffUV.Blue Comparison.RG02 Cumulants
open Next.Rank PhysicalNext.WeightedGaussianMarginal45C.Issue
open scoped BigOperators Classical

variable {I Y : Type} [Fintype I] [DecidableEq I] [Fintype Y]

def slice (B : Y → ℝ) : POL (I ⊕ Y) →ₐ[ℝ] POL I :=
  aeval (Sum.elim MvPolynomial.X (MvPolynomial.C ∘ B))

omit [Fintype I] [DecidableEq I] [Fintype Y] in
@[simp] private theorem free (B : Y → ℝ) (i : I) : slice B (MvPolynomial.X (.inl i)) = MvPolynomial.X i := by
  simp [slice]

omit [Fintype I] [DecidableEq I] [Fintype Y] in
@[simp] private theorem side (B : Y → ℝ) (i : Y) : slice (I:=I) B (MvPolynomial.X (.inr i)) = MvPolynomial.C (B i) := by
  simp [slice]

omit [Fintype I] [Fintype Y] in
private theorem peel (B : Y → ℝ) (i : I) (p : POL (I⊕Y)) :
    slice B (pderiv (.inl i) p) = pderiv i (slice B p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slice]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p j hp =>
    rw [pderiv_mul,map_add,map_mul,map_mul,map_mul,pderiv_mul,hp]
    cases j <;> simp [slice,Pi.single_apply,apply_ite]
    split_ifs <;> simp_all

omit [DecidableEq I] in
private theorem auxiliary (H : Matrix I I ℝ) (p : POL I) (c : ℝ) :
    glaze H (p*MvPolynomial.C c) = glaze H p*MvPolynomial.C c := by
  rw [mul_comm p,mul_comm (glaze H p),C_mul',C_mul',map_smul]

/-- The block Gaussian acts on free keys alone, and commutes with arbitrary
physical values of every coarse spectator. -/
theorem heat (B : Y → ℝ) (Q : Matrix I I ℝ) (p : POL (I⊕Y)) :
    slice B (glaze (fillSlots Y Q) p) = glaze Q (slice B p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slice,glaze_constant]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p t hp =>
    rw [glaze_pin,map_add,map_mul,map_sum,map_mul,Fintype.sum_sum_type]
    cases t with
    | inl j =>
      rw [free,glaze_pin,hp]
      have hp' : slice B (glaze (Matrix.fromBlocks Q 0 0 0) p)=glaze Q (slice B p) := hp
      simp [blend,fillSlots,glaze_deriv,peel,hp']
    | inr j =>
      rw [side,auxiliary,hp]
      simp [blend,fillSlots]

omit [Fintype I] [DecidableEq I] [Fintype Y] in
private theorem project (B : Y → ℝ) (p : POL (I⊕Y)) :
    MvPolynomial.eval B (projectZeroPoly I Y p) = MvPolynomial.constantCoeff (slice B p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slice,projectZeroPoly]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p t hp =>
    simp only [map_mul]
    rw [hp]
    cases t <;> simp [projectZeroPoly,slice]

omit [Fintype I] [DecidableEq I] [Fintype Y] in
/-- Each RG02 real free-field paint has the original coefficient, before
its independent coarse variables are contracted. -/
theorem sampled (B : Y → ℝ) (y : I → ℝ) (p : POL (I⊕Y)) :
    Cloud.paint y (MvPolynomial.map Complex.ofRealHom (slice B p)) = (MvPolynomial.eval (Sum.elim y B) p:ℝ) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slice,Cloud.paint]
  | add p q hp hq =>
    simpa only [map_add,Complex.ofReal_add] using congrArg₂ (·+·) hp hq
  | mul_X p t hp =>
    simp only [map_mul,Complex.ofReal_mul]
    rw [hp]
    cases t <;> simp [Cloud.paint,slice]

/-- Native `Wick` retains the entire coarse-field polynomial. Each of its
lambda coefficients on real fields is exactly the finite complex RG02
moment of the evaluated polynomial, including every Wick pairing. -/
theorem coefficient (B : Y → ℝ) (Q : Matrix I I ℝ) (hs : Q.IsSymm) (P : Ink (I⊕Y)) (i : ℕ) :
    Cloud.wick Q hs 0 (MvPolynomial.map Complex.ofRealHom (slice B (PowerSeries.coeff i P))) =
      (MvPolynomial.eval B (PowerSeries.coeff i (Wick Y Q P)):ℝ) := by
  change aeval (0 : I→ℂ) (Normal.milk (realRank Q hs) _) = _
  rw [PeriodicMarkedHeat.heat_real Q hs,aeval_zero,constantCoeff_map]
  simp only [Wick,projectZero,PowerSeries.coeff_map,overlay_apply]
  change (↑(MvPolynomial.constantCoeff (glaze Q (slice B (PowerSeries.coeff i P)))):ℂ) =
    ↑(MvPolynomial.eval B (projectZeroPoly I Y (glaze (fillSlots Y Q) (PowerSeries.coeff i P))))
  rw [project,heat]

/-- Pointwise on the actual *real* free variables suffices for a complex
RG02 coefficient, even with no holomorphic extension of the field chart. -/
theorem painted (B : Y → ℝ) (Q : Matrix I I ℝ) (hs : Q.IsSymm) (P : Ink (I⊕Y)) (i : ℕ)
    (p : Normal.poly I) (h : ∀ y : I → ℝ, Cloud.paint y p = (MvPolynomial.eval (Sum.elim y B) (PowerSeries.coeff i P):ℝ)) :
    Cloud.wick Q hs 0 p = (MvPolynomial.eval B (PowerSeries.coeff i (Wick Y Q P)):ℝ) := by
  have eq := Valence.Enlist.paint_inj (p:=p) (q:=MvPolynomial.map Complex.ofRealHom (slice B (PowerSeries.coeff i P)))
    (fun y => (h y).trans (sampled B y _).symm)
  rw [eq,coefficient]

end YM.Integration.OriginalFiniteWickReadout
end
