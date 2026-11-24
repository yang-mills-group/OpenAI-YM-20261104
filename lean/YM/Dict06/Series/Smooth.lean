import YM.Dict06.Series.Germ
import YM.Next.FOUNDATIONS.LinkBounds
import Mathlib.Algebra.MvPolynomial.Basic

/-! Polynomial evaluation and pointwise comparison with the diagonal
Fréchet conventions of WilsonX.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Dict06.Series
open YM.Tensor Filter Function YM.Next.Foundations
open scoped BigOperators Topology ContDiff
section Fréchet
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma radial_eq {f : E→F} (n : ℕ) (hf : ContDiffAt ℝ n f 0) (x : E) :
    ordinary n (fun t:ℝ=> f (t • x)) = diagonal (coeff f n 0) x := by
  rw [ordinary,iteratedDeriv_on_line hf]
  rfl

lemma rescale {f : ℝ→F} (n : ℕ) (hf : ContDiffAt ℝ n f 0) (r : ℝ) :
    ordinary n (fun t:ℝ=> f (t*r)) = (r^n) • ordinary n f := by
  calc
    _ = diagonal (coeff f n 0) (r • (1:ℝ)) := by rw [smul_eq_mul,mul_one]; exact radial_eq (E:=ℝ) _ hf _
    _ = _ := by rw [homogeneous,← radial_eq _ hf]; simp

lemma rescale_ps {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    (f : ℝ→R) (hf : ContDiffAt ℝ ∞ f 0) (r : ℝ) (n : ℕ) :
    PowerSeries.coeff n (ps (fun t:ℝ=> f (t*r))) = r^n • PowerSeries.coeff n (ps f) := by
  rw [ps_at,ps_at,rescale n (hf.of_le (WithTop.coe_le_coe.mpr le_top))]
end Fréchet

section comm_ring
variable {I R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R]

/-- Fiberwise evaluation. Reality conditions on f can be imposed on real
t before taking any coefficients; ordinary derivatives of all orders use
only its germ there. -/
def readPoly (f : I→ℝ→R) (p : MvPolynomial I R) (t:ℝ) : R := MvPolynomial.eval (fun i=>f i t) p

def poly (f : I→PowerSeries R) := MvPolynomial.eval₂Hom PowerSeries.C f

lemma readPoly_ps (f : I→ℝ→R) (p : MvPolynomial I R) (hf : ∀ i, ContDiffAt ℝ ∞ (f i) 0) :
    ContDiffAt ℝ ∞ (readPoly f p) 0 ∧ ps (readPoly f p)=poly (fun i=>ps (f i)) p := by
  induction p using MvPolynomial.induction_on with
  | C x =>
    rw [show readPoly f (MvPolynomial.C x) = fun _ => x from funext (fun t=> by simp [readPoly])]
    simp only [poly,MvPolynomial.eval₂Hom_C,ps_const,and_true]; exact contDiffAt_const
  | add p q hp hq =>
    rw [show readPoly f (p+q) = readPoly f p + readPoly f q from funext (fun t=>by simp [readPoly]), _root_.map_add]
    exact ⟨ContDiffAt.add hp.1 hq.1, (ps_add _ _ hp.1 hq.1).trans (congrArg₂ (·+·) hp.2 hq.2)⟩
  | mul_X p i hp =>
    have h (t) : readPoly f (p*MvPolynomial.X i) t= readPoly f p t*f i t := by simp [readPoly]
    rw [show readPoly f _=readPoly f p * f i from funext h,_root_.map_mul]
    refine ⟨ContDiffAt.mul hp.1 (hf i),?_⟩; rw [ps_mul _ _ hp.1 (hf i),hp.2]
    simp [poly]
end comm_ring
end YM.Dict06.Series
