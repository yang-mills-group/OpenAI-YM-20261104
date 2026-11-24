import YM.XSpace.FPS
import YM.XSpace.Hessian
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Taylor vertices in actual link coordinates

An exact polynomial constructor, not pointwise kernel fits. We work with complex
coefficients on real directions (hence extensionality uses equality on a real form).
Taylor lemmas here are for insertions *before Gaussian averaging* in finite dimensions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Taylor
open Function Filter Set Module
open scoped Topology BigOperators ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι] (b : Basis ι ℝ E) {n : ℕ}
abbrev Pol (ι : Type*) := MvPolynomial ι ℂ
open MvPolynomial

def evalAt (x : E) : Pol ι →ₐ[ℂ] ℂ := aeval (fun i=> ((b.repr x i:ℝ):ℂ))
theorem from_real (p q : Pol ι) (he : ∀ x, evalAt b x p=evalAt b x q) : p=q := by
  apply MvPolynomial.funext_set (fun _ => Set.range (fun x : ℝ => (x : ℂ))) (fun _=> infinite_range_of_injective Complex.ofReal_injective)
  intro x hx
  choose y hy using fun i=>hx i (Set.mem_univ i)
  rw [show x=fun i=> ((b.repr (b.equivFun.symm y) i:ℝ):ℂ) by
    funext i; change x i= ((b.equivFun (b.equivFun.symm y) i:ℝ):ℂ); rw [b.equivFun.apply_symm_apply]; exact (hy i).symm]
  exact he _

def tensorVertex (T : E [×n]→L[ℝ] ℂ) : Pol ι := ∑ f : Fin n → ι, C (T (fun i=> b (f i))) * ∏ i, X (f i)
lemma tensorVertex_eval (T : E [×n]→L[ℝ] ℂ) (x : E) : evalAt b x (tensorVertex b T)= T (fun _=>x) := by
  simp only [evalAt,tensorVertex,map_sum,map_mul,map_prod,aeval_C, Algebra.algebraMap_self,RingHom.id_apply,aeval_X]
  have ht:= T.map_sum (fun (_ : Fin n) i=> b.repr x i • b i)
  simp only [b.sum_repr] at ht
  rw [ht]; apply Finset.sum_congr rfl; intro f _
  rw [T.map_smul_univ (fun i=> b.repr x (f i)) (fun i=> b (f i)), Complex.real_smul, Complex.ofReal_prod, mul_comm]

-- Reversals implemented on the polynomial factors, also without picking a pairing order.
def mirror (ι : Type*) : Pol ι →ₐ[ℂ] Pol ι := aeval fun i => -X i
omit [Fintype ι] in
lemma reflected (x : E) (p : Pol ι) : evalAt b x (mirror _ p) = evalAt b (-x) p := by
  change ((evalAt b x).comp (mirror _)) _=_
  congr 1; ext1 i; simp [evalAt,mirror]
lemma reflected_tensor (T : E [×n]→L[ℝ] ℂ) : mirror _ (tensorVertex b T)= C ((-1:ℂ)^n) * tensorVertex b T := by
  apply from_real b; intro x
  rw [reflected,map_mul, tensorVertex_eval,tensorVertex_eval,← neg_one_smul ℝ x,T.map_smul_univ (fun _=> (-1:ℝ)) (fun _=> x)]; simp [Complex.real_smul,evalAt]

-- Real structure (star on these complex coefficients only).
def conjPol (ι : Type*) : Pol ι →+* Pol ι := MvPolynomial.map (starRingEnd ℂ)
omit [Fintype ι] in
lemma eval_conj (x : E) (p : Pol ι) : evalAt b x (conjPol ι p)=star (evalAt b x p) := by
  induction p using MvPolynomial.induction_on with
  | C a=> simp [conjPol,evalAt]
  | add p q hp hq=> rw [map_add,map_add,hp,hq,map_add,star_add]
  | mul_X p i hp=> rw [map_mul,map_mul,hp,map_mul,star_mul, mul_comm]; simp [conjPol,evalAt]

/-- Divided (symmetrization-free) Taylor construction. Use with smoothness receipt when
using derivatives. -/
def divided (n : ℕ) (f : E → ℂ) : Pol ι := C (n.factorial:ℂ)⁻¹ * tensorVertex b (iteratedFDeriv ℝ n f 0)
lemma divided_eval (f : E → ℂ) (x : E) (n : ℕ) : evalAt b x (divided b n f)= (n.factorial:ℂ)⁻¹ * iteratedFDeriv ℝ n f 0 (fun _ => x) := by rw [divided,map_mul,tensorVertex_eval]; simp [evalAt]
lemma divided_zero (f : E → ℂ) : divided b 0 f=C (f 0) := from_real b _ _ (by intro x; rw [divided_eval]; simp [evalAt, iteratedFDeriv_zero_apply])
lemma divided_one (f : E → ℂ) (x : E) : evalAt b x (divided b 1 f)= fderiv ℝ f 0 x:= by simp [divided_eval, iteratedFDeriv_one_apply]
lemma mirror_divided (n : ℕ) (f : E → ℂ) : mirror _ (divided b n f)= (-1)^n * divided b n f := by
  have h:=reflected_tensor b (iteratedFDeriv ℝ n f 0); unfold divided; rw [map_mul,h]; simp [mirror]; ring
lemma divided_realEval (n : ℕ) (f : E → ℝ) (hf : ContDiffAt ℝ (↑n) f 0) (x : E) :
    evalAt b x (divided b n (Complex.ofRealCLM ∘ f))= ↑((n.factorial:ℝ)⁻¹ * iteratedFDeriv ℝ n f 0 (fun _=>x)) := by
  rw [divided_eval, Complex.ofRealCLM.iteratedFDeriv_comp_left hf le_rfl]; push_cast; rfl
lemma divided_real (n : ℕ) (f : E → ℝ) (hf : ContDiffAt ℝ (↑n) f 0) :
    conjPol _ (divided b n (Complex.ofRealCLM ∘ f))=divided b n (Complex.ofRealCLM ∘ f):= by
  apply from_real b; intro x; rw [eval_conj,divided_realEval b n f hf]; simp

def expandTaylor (f : E → ℂ) := PowerSeries.mk fun n=> divided b n f

end YM.XSpace.Taylor
