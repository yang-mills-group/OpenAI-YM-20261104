import YM.RegulatorIR.Budget.TraceGap
import YM.RegulatorIR.Budget.Knot
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Finite-variable component convention. `∑T(z)∏A_z`. No
r-factorial in this formula. Scalar derivatives of the multilinear kernel
must see the *symmetrized* coefficient with norms before dropping labels. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Diagram
open MvPolynomial Function Budget Budget.Layer Budget.Tuple Budget.Packet
open scoped Topology BigOperators Classical
variable {I : Type} {r : ℕ} [Fintype I]
abbrev Jet (I : Type) := MvPolynomial I ℝ

def word (z:Tuple I r): Jet I:= ∏ i,X (z i)
def render (T:Packet I r) : Jet I := ∑ z:Tuple I r, C (T z)*word z
lemma render_add (T U:Packet I r): render (T+U)=render T+render U:=by simp only [render,map_add,Pi.add_apply,add_mul,Finset.sum_add_distrib]
@[simp] lemma render_zero : render (0:Packet I r)=0:=by simp [render]
lemma render_scale (t:ℝ) (T:Packet I r): render (t • T)= C t*render T:=by simp [render,smul_eq_mul, mul_assoc, Finset.mul_sum]
lemma render_sum {Z:Type}{s:Finset Z}(F:Z→Packet I r):render (∑ i∈s,F i)=∑ i∈s,render (F i):=by
 induction s using Finset.induction_on with
 | empty=>simp
 | insert i s h ih=>rw [Finset.sum_insert h,Finset.sum_insert h,render_add,ih]
lemma render_perm (T:Packet I r)(e:Equiv.Perm (Fin r)): render (T ∘ Tuple.perm I e)=render T := by
 unfold render; apply Fintype.sum_equiv (Tuple.perm I e); intro i;change C _ * word i= C _*word (i ∘ e)
 exact congr_arg ((C (T (i ∘ e))) * ·) (Equiv.prod_comp e (fun a=> (X (i a) : Jet I))).symm
lemma render_symmetry (T:Packet I r): render (symmetry T) = render T:=by
 unfold symmetry; rw [render_scale,render_sum]; simp_rw [render_perm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
 let n:= Fintype.card (Equiv.Perm (Fin r))
 rw [← mul_assoc, ← map_natCast (C (σ:=I) (R:=ℝ)) n,← map_mul]; change C ((n:ℝ)⁻¹ * n) * render T= _; unfold n; rw [inv_mul_cancel₀ (by positivity),map_one, one_mul]

omit [Fintype I] in
def slice (T:Packet I (r+1))(x:I): Packet I r:=fun z=> T (Fin.cons x z)
lemma render_cons (T:Packet I (r+1)): render T=∑ x:I,X x*render (slice T x):=by
 unfold render
 rw [← (Tuple.glueEquiv I r).sum_comp, Fintype.sum_prod_type]; apply Finset.sum_congr rfl;intro x _;rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _
 change C (T (Fin.cons x y))* word (Fin.cons x y : Tuple I _)= X x*(C (T (Fin.cons x y))*word y)
 rw [word,Fin.prod_univ_succ];simp [word,mul_left_comm]

omit [Fintype I] in
lemma cons_symm (T:Packet I (r+1))(h:IsSym T)(x:I):IsSym (slice T x):= by
 intro e z; unfold slice
 -- extend permutation by fixing zero
 let f (d:Equiv.Perm (Fin r)) : Fin (r+1) → Fin (r+1):= Fin.cons 0 (Fin.succ ∘ d)
 have hf (d:Equiv.Perm (Fin r)) : Function.LeftInverse (f d.symm) (f d) := by
    intro i; induction i using Fin.cases <;> simp [f]
 let W : Equiv.Perm (Fin (r+1)):= ⟨f e,f e.symm,hf e,hf e.symm⟩
 rw [show (Fin.cons x (z ∘ e):Tuple I (r+1)) = (Fin.cons x z : Tuple I (r+1)) ∘ W from ?_]; exact h W _
 funext i; induction i using Fin.cases <;> simp only [W,Function.comp_apply,Equiv.coe_fn_mk,f,Fin.cons_zero,Fin.cons_succ]
omit [Fintype I] in
lemma second_symm (T:Packet I (r+2))(h:IsSym T)(x y:I): slice (slice T x) y = slice (slice T y) x:= by
 funext i; unfold slice
 let W:Equiv.Perm (Fin (r+2)):=Equiv.swap 0 (0:Fin (r+1)).succ
 rw [show (Fin.cons x (Fin.cons y i):Tuple I (r+2))=(Fin.cons y (Fin.cons x i):Tuple I (r+2)) ∘ W from ?_]; exact h W _
 ext1 a; induction a using Fin.cases
 · simp [W]
 next a=>
   induction a using Fin.cases
   · simp [W]
   next b=>
     have hb : W b.succ.succ=b.succ.succ := Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun he=> Fin.succ_ne_zero b (Fin.succ_inj.mp he))
     simp only [Function.comp_apply,hb,Fin.cons_succ]

lemma pderiv_render (T:Packet I (r+1))(h:IsSym T)(x:I) : pderiv x (render T)= (r+1:Jet I)*render (slice T x):=by
 induction r with
 | zero=>
    rw [render_cons]; simp_rw [map_sum,Derivation.leibniz]
    have H (v:Packet I 0): render v=C (v (Fin.elim0)):=by simp [render,word]; congr
    simp_rw [H, pderiv_C]
    simp [pderiv_X,Pi.single_apply, smul_eq_mul,mul_ite]
 | succ k ih=>
    let R:=slice T x
    calc
      _ = ∑ i:I, (X i * ((k+1:Jet I)*render (slice R i))+(if x=i then render (slice T i) else 0)):= by
             rw [render_cons,map_sum]; refine Finset.sum_congr rfl fun i _=>?_
             rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul,ih _ (cons_symm T h i),second_symm T h i x]; simp only [pderiv_X]; by_cases h:i=x
             · simp [h,R]
             simp [h,Ne.symm h,R]
      _ = (k+1:Jet I)*render R + render (slice T x):=by rw [Finset.sum_add_distrib,render_cons R,Finset.mul_sum]; simp [mul_left_comm]; exact render_cons R
      _ = _:=by change _=(_)*render R; push_cast; unfold R; ring

lemma identified (T U:Packet I r)(h:IsSym T)(hh:IsSym U)(hx:render T=render U): T=U := by
 induction r with
 | zero=>
     have he (T:Packet I 0):render T=C (T Fin.elim0):=by simp [render,word]; congr
     rw [he,he] at hx
     have hs:T Fin.elim0=U Fin.elim0:= C_injective _ _ hx
     ext z; rw [Subsingleton.elim z Fin.elim0];exact hs
 | succ r ih=>
     funext z; obtain ⟨⟨x,y⟩, rfl⟩ := (glueEquiv I r).surjective z
     have he := congr_arg (fun p=> pderiv (R:=ℝ) x p) hx
     change pderiv x (render T)=pderiv x (render U) at he;rw [pderiv_render T h,pderiv_render U hh] at he
     apply congr_fun (ih (slice T x) (slice U x) (cons_symm T h x) (cons_symm U hh x) (mul_left_cancel₀ (by norm_cast) he)) y
lemma homogen (T:Packet I r): MvPolynomial.IsHomogeneous (render T) r:=by
 refine IsHomogeneous.sum _ _ _ (fun z _=>?_)
 apply IsHomogeneous.C_mul
 simpa [word] using IsHomogeneous.prod (R:=ℝ) (Finset.univ (α:=Fin r)) (fun i=> X (z i)) (fun _=> 1) (fun i _=> isHomogeneous_X ..)
lemma isolate {z:Finset ℕ} (T:(k:ℕ)→Packet I k) (h:r∈z): homogeneousComponent r (∑ i∈z, render (T i))=render (T r):=by
 simp_rw [map_sum, homogeneousComponent_of_mem (homogen (T _)), Finset.sum_ite_eq,h,ite_true]
end YM.RegulatorIR.Diagram
