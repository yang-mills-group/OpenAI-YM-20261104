import YM.MSbar.Cacao.Melt
import YM.MSbar.Cacao.Stein
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Cacao
open MeasureTheory Filter Function Finset Matrix PowerSeries
open ProbabilityTheory MvPolynomial
open scoped Topology BigOperators Classical ENNReal NNReal ContDiff
variable {σ ι : Type} [Fintype ι][Fintype σ][DecidableEq ι][DecidableEq σ]
open Further.GaussianScalar
local notation "p!"=> fieldLaw
local notation "H"=> View ι
local notation "V"=> View σ
local notation "P"=> Pot σ
variable {g : Matrix ι ι ℝ}(v : Matrix σ ι ℝ) (h:g.PosDef)
omit [DecidableEq σ] in
lemma vent (p:P): ContDiff ℝ ω (fun y:View σ=>MvPolynomial.eval y p):=by
    induction p using MvPolynomial.induction_on with
    | C a=> simp only [eval_C]; fun_prop
    | add p q hp hq=> simp_rw [map_add]; exact hp.add hq
    | mul_X p c hp=>simp_rw [map_mul,eval_X]; exact hp.mul (((ContinuousLinearMap.proj c:View σ→L[ℝ]ℝ)).contDiff)
local notation "k!"=> v*g*v.transpose
include h
lemma rootedG : IsGaussian (fieldLaw g) := by
    unfold fieldLaw; change IsGaussian (Measure.map (↑(PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ))) _); infer_instance -- invalid
lemma grille (p:P) (x:V)(u:ℝ≥0∞) (hu:u≠⊤) : MemLp (fun y:View ι=> MvPolynomial.eval (x+v *ᵥ y) p) u (fieldLaw g) :=by
   haveI:=rootedG h
   induction p using MvPolynomial.induction_on generalizing u with
   | C a=> simp only [eval_C]; exact memLp_const _
   | add p q hp hq=> simp_rw [map_add]; exact (hp u hu).add (hq _ hu)
   | mul_X p c hp=>
       simp_rw [map_mul,eval_X, Pi.add_apply]; let q:=2*u; have he: q≠⊤:= ENNReal.mul_ne_top (by norm_num) hu
       let A: H →L[ℝ] ℝ := (ContinuousLinearMap.proj c).comp (LinearMap.toContinuousLinearMap (toLin' v))
       have hh : MemLp (fun t:H=>(x+v *ᵥ t) c) q (fieldLaw g):= (memLp_const (x c)).add (IsGaussian.memLp_dual (fieldLaw g) A q he)
       haveI : ENNReal.HolderTriple q q u:= ⟨by unfold q; rw [← two_mul,ENNReal.mul_inv,←mul_assoc,ENNReal.mul_inv_cancel (by norm_num) (by norm_num),one_mul] <;> simp⟩
       apply MemLp.mul' hh (hp _ he)
       -- ENNReal.Typeclass...
lemma trunk (a b:σ): (v*g*v.transpose) a b=(v*g*v.transpose) b a:=by
    change (v*g*v.transpose) a b= (v*g*v.transpose).transpose a b; have ht:g.transpose=g:=by simpa [IsHermitian] using h.1
    rw [Matrix.transpose_mul,Matrix.transpose_mul,transpose_transpose,ht,Matrix.mul_assoc] -- [Matrix.transpose_mul,ht,Matrix.mul_assoc] -- simp mul maybe loop
omit h in
def dir_G (i : σ)(v:Matrix σ ι ℝ)(g:Matrix ι ι ℝ): View ι:= (g *ᵥ fun j=> v i j)
set_option quotPrecheck false
variable (x: View σ)
local notation "η"=> (fun r:View ι=> x+v *ᵥ r)
local notation "μ!"=> fieldLaw g
-- line derivative under shifts exactly
lemma traces (j:σ)(m : H): v *ᵥ dir_G j v g = fun a=> (k!) j a := by
    funext i; unfold dir_G; rw [trunk v h]; change dotProduct _ (g *ᵥ (fun x=> v j x))= dotProduct (fun x=>(v*g) i x) _; rw [dotProduct_mulVec]; congr 1 -- rfl
lemma terrace (i:σ)(t:H) : dotProduct (g⁻¹ *ᵥ t) (dir_G i v g)= η t i- x i :=by
    unfold dir_G; rw [dotProduct_mulVec,← mulVec_transpose]; have ht:g.transpose=g:=by simpa [IsHermitian] using h.1
    rw [ht,mulVec_mulVec,g.mul_nonsing_inv (isUnit_iff_ne_zero.mpr h.det_pos.ne'),one_mulVec,dotProduct_comm t]; change (v *ᵥ t) i= x i+(v *ᵥ t) i-x i; abel
lemma twigs (b:P)(i:σ)(y:View ι): HasDerivAt (fun t:ℝ=> MvPolynomial.eval (η (y+t • dir_G i v g)) b) (MvPolynomial.eval (η y) ((tureen (v*g*v.transpose) i) b)) 0:=by
   let f := η; induction b using MvPolynomial.induction_on with
   | C a=> simp [drink]; exact hasDerivAt_const ..
   | add p q hp hq=> simp_rw [map_add]; exact hp.add hq
   | mul_X p c hp=>
       let k':=v*g*v.transpose; have hv: ∀ t:ℝ,η (y+t • dir_G i v g) c=η y c + t*k' i c:=by intro t; dsimp only; rw [Matrix.mulVec_add,Matrix.mulVec_smul, traces v h _ y,← add_assoc]; simp [k']
       have hL (i:σ)(p q:P): tureen k' i (p*q)=tureen k' i p*q+p*tureen k' i q:=by rw [drink,drink,drink,sum_mul,mul_sum,← sum_add_distrib]; refine sum_congr rfl fun j _=>?_ ; rw [pderiv_mul,smul_add,mul_smul_comm,smul_mul_assoc]
       have hc: (tureen k' i) (MvPolynomial.X c)= k' i c • (1:P) := by rw [drink]; simp [pderiv_X,Pi.single_apply,smul_ite] -- order
       rw [show tureen (v*g*v.transpose) i _= tureen k' i p * MvPolynomial.X c + p*(k' i c • (1:P)) from by rw [← hc]; exact hL ..]; simp only [_root_.map_mul,_root_.map_add, eval_X,← C_mul',eval_C,_root_.map_one]
       convert! hp.mul (((hasDerivAt_id' 0).mul_const (k' i c)).const_add (η y c)) using 1
       · ext t; change _* η _ c= _*(η y c+ t*k' i c); rw [hv]
       simp [k']
lemma peas (p:P) (i:σ) :
       (∫ r:View ι, MvPolynomial.eval (x+v *ᵥ r) (p*MvPolynomial.X i)∂fieldLaw g)= (∫ r:View ι,MvPolynomial.eval (x+v *ᵥ r) p∂fieldLaw g)*x i+
       ∫ r:View ι, MvPolynomial.eval (x+v *ᵥ r) ((tureen (v*g*v.transpose) i) p)∂fieldLaw g:=by
    let F(p:P)(r:H):= eval (η r) p; have hg(p:P):Continuous (F p):= (vent p).continuous.comp (continuous_const.add ((toLin' v).continuous_of_finiteDimensional))
    have hi(p:P):Integrable (F p) (fieldLaw g):=(grille v h p x 1 (by norm_num)).integrable (le_refl _)
    let u(r):=dotProduct (g⁻¹ *ᵥ r) (dir_G i v g)*F p r; have he: ∀ r:H,u r = F (p*MvPolynomial.X i) r-F p r*x i:=by intro r; unfold u;rw [terrace]; unfold F; simp only [map_mul, eval_X]; ring; exact h -- terrace args
    have ht:Integrable u (fieldLaw g):=by simp_rw [funext he]; exact (hi _).sub ((hi _).mul_const _)
    have hz:= steamed h (dir_G i v g) (hg _) (hg _) (hi p) (hi ((tureen (v*g*v.transpose) i) p)) ht (twigs v h x p i)
    let T:=fieldLaw g; change (∫ z,F _ z∂T)= (∫ z,u z∂T) at hz; rw [show (∫ z,u z∂T)= (∫ z,F (p*MvPolynomial.X i) z∂ T)-(∫ z,F p z∂T)*x i from ?_] at hz; exact (eq_add_of_sub_eq' hz.symm) -- arguments
    rw [funext he, integral_sub (hi _) ((hi _).mul_const _),integral_mul_const]
end YM.MSbar.Cacao
