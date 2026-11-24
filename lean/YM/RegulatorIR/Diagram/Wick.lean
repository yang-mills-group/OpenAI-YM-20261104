import YM.RegulatorIR.Diagram.Stein

/-!
Heat/Wick identity by induction, with a triangular property on *any*
ambient leg derivatives simultaneously. No representational choice of
full-ambient inverse covariance enters this proof. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Diagram.Gaussian
open Function MvPolynomial Interval Formal Polynomial Budget Budget.Layer Finset MeasureTheory PertExtension Series GaussianScore
open scoped Topology BigOperators Classical PowerSeries Polynomial
variable {I E : Type}[Fintype I][NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
  (A:Law E) (d:I→Module.Dual ℝ E) [MeasurableSpace E] [BorelSpace E] (μ:Measure E)[μ.HasTemperateGrowth]
variable {K : Layer I I}

def chains (P: CurveT I) : List I→CurveT I
| []=> P
| i::is=> chains (blade i P) is
omit [Fintype I] in
lemma chain_add (P Q:CurveT I)(i:List I): chains (P+Q) i= chains P i+chains Q i:=by induction i generalizing P Q with
 | nil=> rfl
 | cons a l ih=>rw [chains,map_add,ih];rfl
omit [Fintype I] in
@[simp] lemma chain_zero (i:List I):chains 0 i=0:=by induction i with
 | nil=>rfl
 | cons a l ih=>rw [chains,map_zero,ih]

-- sampling, prior to deterministic mean transmission

def hear (Q : CurveT I)(b:I→ℝ):= MvPolynomial.eval b (Q.eval 1)
omit [Fintype I] in
lemma hear_sum (P Q:CurveT I)(b:I→ℝ): hear (P+Q) b=hear P b+hear Q b:=by unfold hear; rw [Polynomial.eval_add,MvPolynomial.eval_add]
-- invariant with derivatives for induction

def Access (Q : CurveT I):Prop:=∀ (k:List I) (b:I→ℝ), averaged A d μ b ((chains Q k).coeff 0)= hear (chains Q k) b
omit [Fintype I] in
lemma access_add (P Q : CurveT I)(h:Access A d μ P)(hh:Access A d μ Q):Access A d μ (P+Q):=by
 intro k b; rw [chain_add,Polynomial.coeff_add, hear_sum, average_add, h,hh]
omit [Fintype I] [FiniteDimensional ℝ E] [BorelSpace E] [μ.HasTemperateGrowth] in
lemma differentiated (P:CurveT I)(h:Access A d μ P)(i:I): Access A d μ (blade i P):=fun k b=> h (i::k) b

lemma rise_origin (K:Layer I I)(i:I)(P:CurveT I) : (augment K i P).coeff 0=P.coeff 0* MvPolynomial.X i:=by simp_rw [Polynomial.coeff_zero_eq_eval_zero,augment]; simp [axis]
lemma apex (K:Layer I I)(P:CurveT I)(b:I→ℝ)(i):
    hear (augment K i P) b=b i*hear P b + ∑ j, K i j*hear (blade j P) b :=by
 unfold hear augment react
 rw [Polynomial.eval_add,Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_X,one_mul]; simp only [axis,Polynomial.eval_C,Polynomial.eval_finsetSum,MvPolynomial.eval_add,MvPolynomial.eval_mul,MvPolynomial.eval_X,MvPolynomial.eval_sum]; rw [mul_comm]; apply congr_arg
 -- evaluate terms
 simp_rw [Polynomial.eval_smul,Algebra.smul_def,show ∀ t:ℝ,algebraMap ℝ (Jet I) t=MvPolynomial.C t from fun _=>rfl,MvPolynomial.eval_mul,MvPolynomial.eval_C]

variable [NeZero μ] [μ.IsAddRightInvariant]
omit [NeZero μ] in
lemma access_augment (P:CurveT I)(h:Access A d μ P)(i:I):Access A d μ (augment (bond A d) i P):=by
 let K:=bond A d; intro k
 induction k generalizing P with
 | nil =>
    intro b
    change averaged A d μ b ((augment K i P).coeff 0)=hear (augment K i P) b
    rw [apex,rise_origin,recipe]
    congr 1
    · exact congr_arg (b i * ·) (h [] b)
    exact Finset.sum_congr rfl fun j _=>by
       rw [show MvPolynomial.pderiv j (P.coeff 0)= (blade j P).coeff 0 from Eq.symm (remaining_v ..)]; exact congr_arg (K i j * ·) (h [j] b)
 | cons a l ih =>
    intro b
    simp_rw [chains,push_chart]; split
    · rw [chain_add, hear_sum,Polynomial.coeff_add,average_add]
      exact congr_arg₂ (·+·) (ih (blade a P) (differentiated A d μ P h a) b) (h ..)
    rw [add_zero]; exact ih _ (differentiated A d μ P h a) b
lemma heat_exists (u:Jet I) : ∃ p:CurveT I,p.coeff 0=u ∧ Pursues (bond A d) p ∧ Access A d μ p := by
 induction u using MvPolynomial.induction_on with
 | C r=>
    refine ⟨Polynomial.C (MvPolynomial.C r),by simp, thermal_const ..,fun k b=>?_⟩
    cases k with
    | nil=> simp_rw [chains,Polynomial.coeff_C_zero]; rw [average_const]; simp [hear]
    | cons a l=>rw [chains,blade_C, MvPolynomial.pderiv_C,map_zero,chain_zero,Polynomial.coeff_zero]; have hv:=average_const A d b μ 0; rw [map_zero] at hv; rw [hv]; simp [hear]
 | add x y h k=>
    obtain ⟨u,h₁,h₂,h₃⟩:= h;obtain ⟨v,t₁,t₂,t₃⟩:=k
    exact ⟨u+v,by simp [h₁,t₁], thermal_add h₂ t₂,access_add _ _ _ _ _ h₃ t₃⟩
 | mul_X x i h=>
    obtain ⟨p,h₁,h₂,h₃⟩:=h
    exact ⟨augment (bond A d) i p,by rw [rise_origin,h₁],thermal_augment h₂ (bond_cross A d) _,access_augment A d μ p h₃ i⟩
lemma heat_identity (Q:CurveT I)(h:Pursues (bond A d) Q) (b:I→ℝ):averaged A d μ b (Q.coeff 0)= hear Q b:=by
 obtain ⟨p,h₁,h₂,h₃⟩:= heat_exists A d μ (Q.coeff 0)
 rw [Interval.unique p Q h₂ h h₁] at h₃; exact h₃ [] b
end YM.RegulatorIR.Diagram.Gaussian
