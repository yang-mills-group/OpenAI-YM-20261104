import YM.PertExtension.GaussianIBP
import YM.Next.RANK.Common
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# The complete complex polynomial Wick readout of a Hessian

First part of the Fk/RG10 and Orb/XSpace/MS bridges. Generalizes the real-projection lemma in
`YM.PertExtension.PolynomialWick` from Orb's particular Hessian, and retains arbitrary
complex coefficients. No positivity of the matrix on *slots*, nor independence of repeated slots,
is needed. We include the compatibility with the basis Hessian convention of `XSpace.Bare`.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.FVA2.Wick
open Function Set Filter Module MeasureTheory Finset MvPolynomial
open PertExtension PertExtension.Series PertExtension.GaussianScore
open Next.Rank Next.Rank.Normal
open scoped Topology ContDiff BigOperators Classical ENNReal
variable {E I : Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable (Γ : Law E) (S : I → Module.Dual ℝ E)

/-- Complexification of the real covariance (bilinear extension, NO conjugation). -/
def color : Symmetric I where
  cov i j := (Γ.wick (S i) (S j) : ℂ)
  symm i j := congr_arg Complex.ofReal (calc
      (S j) (Γ.inverse (S i)) = Γ.P (Γ.inverse (S j)) (Γ.inverse (S i)) := by rw [Γ.applies]
      _ = Γ.P (Γ.inverse (S i)) (Γ.inverse (S j)) := Γ.turns _ _
      _ = (S i) (Γ.inverse (S j)) := by rw [Γ.applies])

variable [MeasurableSpace E][BorelSpace E]
variable (μ : Measure E)[μ.HasTemperateGrowth][μ.IsAddRightInvariant][NeZero μ]

lemma monomial_wick {V : Type*} (f : V→I) (A : Finset V) :
    (Γ.average μ (Law.product (S ∘ f) A) : ℂ) = blend (color Γ S) 0 (glyphs f A) := by
  classical
  induction A using Finset.strongInduction with
  | H s ih =>
    obtain rfl|⟨i,hi⟩:=s.eq_empty_or_nonempty
    · rw [show Law.product (S ∘ f) (∅:Finset V) = 1 from funext (fun _=> prod_empty), Law.empty,
          glyphs, Finset.prod_empty, fresh, Complex.ofReal_one]
    let t:= s.erase i
    have h₁ : i ∉ t := notMem_erase i s
    have h₂ : s=insert i t := (insert_erase hi).symm
    have hs : t ⊂ s := erase_ssubset hi
    rw [h₂, show Law.product (S ∘ f) (insert i t) =
      (fun x=> Law.product (S ∘ f) t x * S (f i) x) from ?_, Law.recursion, spring 0 (color Γ S) f t h₁]
    · rw [Pi.zero_apply,zero_mul,zero_add,Complex.ofReal_sum]
      refine sum_congr rfl fun j hj=> ?_
      rw [Complex.ofReal_mul, ih (t.erase j) (Finset.ssubset_of_subset_of_ssubset (erase_subset ..) hs)]
      exact mul_comm ..
    funext x; unfold Law.product; rw [prod_insert h₁]; exact mul_comm ..

/-- Expectation evaluating at these real linear slots. -/
def evaluation (x:E) (p:poly I) := aeval (R:=ℂ) (fun i=> ((S i x:ℝ):ℂ)) p * (Γ.kern x:ℂ)

def report (p:poly I) : ℂ := (∫ x,evaluation Γ S x p ∂μ) / ↑(∫ x, Γ.kern x ∂μ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma eval_glyph {V : Type*} (f: V→I)(s:Finset V)(x:E):
    evaluation Γ S x (glyphs f s)= (((Law.product (S ∘ f) s x * Γ.kern x:ℝ):ℂ)):= by
  simp [evaluation,glyphs,Law.product,Function.comp_apply]

omit [μ.IsAddRightInvariant] [NeZero μ] in
lemma integrable_glyph {V : Type*} (f: V→I)(s:Finset V) :
    Integrable (fun x=> evaluation Γ S x (glyphs f s)) μ := by
  simp_rw [eval_glyph]; exact (Γ.integrable_entry μ (Law.product_bound _ s) (Law.product_cont ..)).ofReal

lemma report_glyph {V : Type*}(f : V → I)(s: Finset V):
      report Γ S μ (glyphs f s)= blend (color Γ S) 0 (glyphs f s):=by
    let K:= Law.product (S ∘ f) s * Γ.kern
    have hK: Integrable K μ:= Γ.integrable_entry μ (Law.product_bound _ _) (Law.product_cont ..)
    have he := Complex.ofRealCLM.integral_comp_comm hK
    unfold report; simp_rw [eval_glyph]; rw [show (∫ x:E, ((Law.product _ s x * Γ.kern x:ℝ):ℂ) ∂μ)=_ from he]
    rw [← monomial_wick Γ S μ f]; exact (Complex.ofReal_div ..).symm
private lemma cert (p:poly I) : Integrable (fun x=>evaluation Γ S x p) μ ∧
    report Γ S μ p = blend (color Γ S) 0 p := by
  -- finite polynomial support
  choose f hf using (fun a:I→₀ℕ=> Common.letter a)
  let K := color Γ S
  let g (a:I→₀ℕ): poly I:= glyphs (f a) univ
  let d a:= coeff a p
  have hs : p = ∑ a∈p.support,d a • g a:= by
    conv_lhs => rw [p.as_sum];
    refine sum_congr rfl fun a _=> ?_
    dsimp only [g,d]; rw [← hf a,← map_smul,smul_eq_mul,mul_one]
  rw (occs:=.pos [1,2,3]) [hs]
  have hv (x:E) : evaluation Γ S x (∑ a∈p.support,d a • g a)=∑ a∈p.support,d a * evaluation Γ S x (g a) := by
    unfold evaluation; rw [map_sum,sum_mul]; refine sum_congr rfl fun a _=>?_; rw [map_smul, smul_eq_mul,mul_assoc]
  unfold report; simp_rw [hv]; have hG (i:I→₀ℕ) : Integrable (fun x=> d i * evaluation Γ S x (g i)) μ := (integrable_glyph Γ S μ (f i) univ).const_mul _
  constructor
  · exact MeasureTheory.integrable_finsetSum (f:=fun i x=> d i * evaluation Γ S x (g i)) p.support fun i _=> hG i
  rw [MeasureTheory.integral_finsetSum _ (fun i _=> hG i),Finset.sum_div,map_sum]; refine sum_congr rfl fun a _=>?_
  rw [MeasureTheory.integral_const_mul,map_smul,smul_eq_mul,mul_div_assoc]; exact congr_arg (d a * ·) (report_glyph Γ S μ (f a) univ)

theorem integrable_eval (p:poly I): Integrable (fun x=>evaluation Γ S x p) μ := (cert Γ S μ p).1

theorem report_eq (p:poly I) : report Γ S μ p= blend (color Γ S) 0 p := (cert Γ S μ p).2

variable [Fintype I][DecidableEq I]

private abbrev matCov (c : Basis I ℝ E) : Matrix I I ℝ:=fun i j=>Γ.wick (c.coord i) (c.coord j)

omit [MeasurableSpace E] [BorelSpace E] in
lemma basis_cov (c : Basis I ℝ E)(i j:I) :
    Γ.wick (c.coord i) (c.coord j) = ((LinearMap.BilinForm.toMatrix c Γ.P : Matrix I I ℝ)⁻¹) i j := by
  apply Eq.symm; suffices h : ((LinearMap.BilinForm.toMatrix c Γ.P : Matrix I I ℝ)⁻¹)=matCov Γ c from
    congr_fun (congr_fun h i) j
  refine Matrix.inv_eq_left_inv ?_
  ext k l; rw [Matrix.mul_apply,Matrix.one_apply];
  simp_rw [LinearMap.BilinForm.toMatrix_apply]; let b:=Γ.inverse (c.coord k)
  change (∑ i,(c.coord i b) * (Γ.P (c i) (c l)))=_
  have he : Γ.P b (c l) = ∑ i,(c.coord i b) * Γ.P (c i) (c l):= by
    conv_lhs=> rw [← c.sum_repr b,map_sum,LinearMap.sum_apply];
    exact sum_congr rfl fun i _=> by rw [map_smul,LinearMap.smul_apply,Basis.coord_apply,smul_eq_mul]
  rw [← he]
  unfold b; rw [Γ.applies, Basis.coord_apply, c.repr_self_apply]; by_cases h:l=k
  · simp [h]
  rw [if_neg h,if_neg (Ne.symm h)]
end YM.FVA2.Wick
