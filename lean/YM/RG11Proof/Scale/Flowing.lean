import YM.RG11Proof.Scale.Portable
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Engineering powers with log corrections from triangular formal CS

For use on FINAL mass-independent scales through N. Require slope and
constant of CS coupling beta *both* zero. Require b has zero constant and
preserves grades in all positive powers employed (prove from mass-independent
scheme, not from THE SOUGHT MATCH). Then through order N Euler derivative
represented by another tested profile can be integrated to exact power-log on
all scales, for every announced position horizon. Thus in the test criterion,
if on each array this derivative can be evaluated for any scaled profile using
CS (e.g. integral from `GaugeEuler` or LF continuity), same profiles as
matching, the Engineering assumptions in `stamp_transport` can be discharged
WITHOUT a further mass-independent law of the conversion itself. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG11.Scale
open scoped BigOperators Topology Classical
open PowerSeries YM.PertExtension.Position YM.RG11.Jets
variable {P J : Type*}{width:P→ℕ}[Fintype J]

-- growth as functions on ALL ℝ
def fulcrum (w:ℝ):Submodule ℝ (ℝ→ℝ) where
  carrier:={f |∃ p:Polynomial ℝ,∀u:ℝ,f u=Real.exp (w*u)*p.eval u}
  zero_mem':=⟨0,fun _=>by simp⟩
  add_mem':=by rintro v f ⟨p,h⟩ ⟨q,H⟩; exact ⟨p+q,fun u=>by simp [h,H,mul_add]⟩
  smul_mem':=by rintro z f ⟨p,h⟩; exact ⟨Polynomial.C z * p,fun u=>by simp only [h,Pi.smul_apply, Polynomial.eval_C_mul,smul_eq_mul]; ring⟩

private theorem primitive (p:Polynomial ℝ):∃ q:Polynomial ℝ,Polynomial.derivative q=p:=by
  induction p using Polynomial.induction_on' with
  | add p q hp hq=>obtain ⟨p',h⟩:=hp; obtain ⟨q',hq⟩:=hq; use p'+q'; rw [map_add,h,hq]
  | monomial n c=>
     use Polynomial.monomial (n+1) (c/(n+1:ℕ))
     rw [Polynomial.derivative_monomial_succ]; simp [show (n:ℝ)+1≠0 by positivity]

private theorem derivative_fulcrum {f' f:ℝ→ℝ}{w:ℝ}(h:f'∈ fulcrum w)
   (he:∀u:ℝ,HasDerivAt f (w*f u+f' u) u): f∈ fulcrum w:=by
  obtain ⟨p,hp⟩:= h
  obtain ⟨q,hq⟩:=primitive p
  let F(u:ℝ):=Real.exp (-w*u)*f u - q.eval u
  have hc (u:ℝ):HasDerivAt F 0 u:=by
     have ht : HasDerivAt (fun u=>Real.exp (-w*u)) ((-w)*Real.exp (-w*u)) u:=by simpa [Function.comp_def,mul_comm (-w)] using
        ((hasDerivAt_id' u).const_mul (-w)).exp
     have hw:= (ht.mul (he u)).sub (q.hasDerivAt u)
     rw [hq,hp u] at hw
     have hv:= Real.exp_neg (- -(w*u))
     convert! hw using 1
     simp only [neg_mul,Real.exp_neg]
     field_simp
     ring
  have heq (u:ℝ): F u= F 0:=is_const_of_deriv_eq_zero (fun y=>(hc y).differentiableAt) (fun y=>(hc y).deriv) u 0
  use Polynomial.C (F 0)+q; intro u; rw [Polynomial.eval_add,Polynomial.eval_C, ← heq u]; unfold F
  rw [sub_add_cancel,←mul_assoc,neg_mul, Real.exp_neg,mul_inv_cancel₀ (Real.exp_ne_zero _),one_mul]

/-- Compatibility of evaluation differentiation with exact shape Euler E, on
coefficients incl all powers through N IN A SINGLE array. -/
def Respiration (s:ℝ→Keeper width)(E:Keeper width)(A:ArrayAt J ℝ width)(N:ℕ): Prop:=
   ∀ k≤N,∀ (v:Mark J width) (u:ℝ),HasDerivAt (fun t:ℝ=>coeff k (A ((s t).move v))) (coeff k (A (E.move ((s u).move v)))) u

-- bulk invariant despite retagging
theorem bulk_cast (s:Keeper width)(w:J→ℕ)(v:Mark J width):bulk w (s.move v)=bulk w v:=by
   let n:=width v.1
   let m:=width (s.profile v.1)
   let e:m=n:=(s.size v.1).symm
   have he : ∀ (i: Fin n→J) (k:ℕ)(h:k=n), ∑ a:Fin k,(w (i (Fin.cast h a)):ℝ)=∑ a:Fin n,(w (i a):ℝ):=by intro i k h; subst k; rfl
   apply he v.2 _ _

-- start beta and b with the displayed vanishers
 theorem logarithms {s:ℝ→Keeper width}(w:J→ℕ)(E:Keeper width){A:ArrayAt J ℝ width}{N}
    {β:PowerSeries ℝ}{b:Square J (PowerSeries ℝ)}(hp:Stem N E w A β b)(he:Respiration s E A N)
    (hb:∀ k≤1,coeff k β=0)(hZ:piece 0 b=0)(hX:∀ k≤N,graded w (piece k b)):
    ∀ k≤N,∀ v:Mark J width,(fun u:ℝ=>coeff k (A ((s u).move v)))∈fulcrum (bulk w v):=by
   intro k hk
   induction k using Nat.strong_induction_on with
   | h k ih=>
   intro v
   refine derivative_fulcrum (f':=fun u:ℝ=>coeff k (call β b A ((s u).move v))) ?_ ?_
   · let W:=bulk w v
     let L(i:Fin (width v.1))(j:J):Mark J width:=⟨v.1,Function.update v.2 i j⟩
     let g(i:ℕ)(z:Mark J width)(u:ℝ):= coeff i (A ((s u).move z))
     have hi i (hx:i<k) z:g i z∈fulcrum (bulk w z):=ih i hx (hx.le.trans hk) z
     have H(x:ℕ × ℕ)(hh:x.1+x.2=k) :
         (fun u:ℝ=>coeff x.1 β * (g (x.2+1) v u * (x.2+1)))∈ fulcrum W:=by
        by_cases ht:x.1≤1
        · simp_rw [hb x.1 ht,zero_mul]; exact (fulcrum W).zero_mem
        rw [show (fun u:ℝ=> _ * (g (x.2+1) v u * _))=(coeff x.1 β * (x.2+1)) • g (x.2+1) v from funext fun u=>by change coeff x.1 β * (_ * (x.2+1))=(_ * (x.2+1)) * _; ring]
        exact Submodule.smul_mem _ _ (hi _ (by omega) v)
     have H'(i:Fin (width v.1))(j:J)(x:ℕ × ℕ)(hz:x.1+x.2=k):
         (fun u:ℝ=>piece x.1 b (v.2 i) j * g x.2 (L i j) u)∈ fulcrum W:=by
        by_cases he:w (v.2 i)=w j
        · by_cases hx:x.1=0
          · rw [hx,hZ]; simp only [Matrix.zero_apply, zero_mul]; exact (fulcrum W).zero_mem
          apply Submodule.smul_mem _ (piece _ _ _ _)
          have hL:W=bulk w (L i j):= by
            unfold W bulk; apply Finset.sum_congr rfl; intro l _
            by_cases hu:l=i
            · subst i; simp [L,he]
            simp [L,Function.update_of_ne hu]
          rw [hL]; exact hi x.2 (by omega) _
        simp_rw [@hX x.1 (by omega) (v.2 i) j he, zero_mul]; exact (fulcrum W).zero_mem
     apply Submodule.sub_mem (fulcrum W) (x:=fun u=>coeff k (β*derivative ℝ (A ((s u).move v)))) (y:=fun u=>coeff k (orbit A ((s u).move v) b)) _ _ -- goal not definitionally subtraction?
     · have ht:(∑ x∈Finset.HasAntidiagonal.antidiagonal k,(fun u:ℝ=>coeff x.1 β*(g (x.2+1) v u * (x.2+1))))∈fulcrum W:=Submodule.sum_mem _ (fun x hx=>H x (Finset.HasAntidiagonal.mem_antidiagonal.mp hx))
       convert! ht using 1; ext u; simp [coeff_mul,coeff_derivative,g]
     simp_rw [Keeper.move_orbit,orbit,map_sum,coeff_mul, Function.comp_apply]
     have ht:=Submodule.sum_mem (fulcrum W) (t:=Finset.univ (α:=Fin (width v.1))) (fun i hi=>Submodule.sum_mem (fulcrum W) (t:=(Finset.univ (α:=J))) (fun j hj=>Submodule.sum_mem _ (t:=Finset.HasAntidiagonal.antidiagonal k) (f:=fun x=>fun u:ℝ=>piece x.1 b (v.2 i) j*g x.2 (L i j) u) (fun x hx=>H' i j x (Finset.HasAntidiagonal.mem_antidiagonal.mp hx))))
     convert! ht using 1; ext u; simp only [Finset.sum_apply,piece_apply,L,g]

   · intro u
     have hq:= he k hk v u
     rw [←hp ((s u).move v) k hk,euler,map_sub,coeff_C_mul,bulk_cast]; ring_nf
     convert! hq using 1
end YM.RG11.Scale
