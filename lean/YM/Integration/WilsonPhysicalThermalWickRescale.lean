import YM.Next.RANK.GaussSubst
import YM.Next.RANK.GaussTags
import YM.Next.RANK.Common
import YM.Next.RANK.ScaleJet

/-! Reciprocal changes of the original two groups of Gaussian coordinates.
They leave every between-site contraction unchanged. Polynomials homogeneous
in the numbers of curvature legs acquire one scalar on each ordinary face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickRescale
open Finset MvPolynomial Function
open Next.Rank.Normal Next.Rank.Perch
open scoped BigOperators Classical
variable {V:Type*}

def edit (a:Fin 2→ℂ)(i:Fin 2 × V):(Fin 2 × V)→₀ℂ:=Finsupp.single i (a i.1)

theorem cov (a:Fin 2→ℂ)(Q:Symmetric (Fin 2 × V))(i j:Fin 2 × V):
    (scope (edit a) Q).cov i j=a i.1*a j.1*Q.cov i j:=by
  simp [edit,scope,treats,Finsupp.linearCombination_single,Pi.smul_apply,smul_eq_mul]
  ring

theorem mean (a:Fin 2→ℂ)(μ:Fin 2 × V→ℂ)(i:Fin 2 × V):
    reads (edit a) μ i=a i.1*μ i:=by
  simp [edit,reads,Finsupp.linearCombination_single,smul_eq_mul]

def pure (q:ℕ)(p:poly V):Prop:=∀m∈p.support,Finsupp.weight (fun _:V=>1) m=q

theorem degree (q:ℕ)(p:poly V)(h:pure q p)(a:ℂ):jets (fun _:V=>1) a p=a^q • p:=by
  ext1 m
  rw [jets_coeff,coeff_smul,smul_eq_mul]
  by_cases e:m∈p.support
  · rw [h _ e]
  · rw [notMem_support_iff.mp e,mul_zero,mul_zero]

private theorem post_change (a:Fin 2→ℂ)(i:Fin 2)(p:poly V):
    exchange (edit a) (post i p)=post i (jets (fun _:V=>1) (a i) p):=by
  have maps:(exchange (edit (V:=V) a)).comp (post i)=(post i).comp (jets (fun _:V=>1) (a i)):=by
    ext x
    simp [post,jets,edit,glyph,Finsupp.linearCombination_single,Algebra.smul_def]
  exact DFunLike.congr_fun maps p

theorem face (a:Fin 2→ℂ)(p:Fin 2→poly V)(q:Fin 2→ℕ)(h:∀i,pure (q i) (p i))(S:Finset (Fin 2))
    (Q:Symmetric (Fin 2 × V))(μ:Fin 2 × V→ℂ):
    blend (scope (edit a) Q) (reads (edit a) μ) (pot S p)=
      (∏i∈S,(a i)^(q i))*blend Q μ (pot S p):=by
  rw [←wets]
  suffices scaled:exchange (edit a) (pot S p)=(∏i∈S,(a i)^(q i)) • pot S p by
    rw [scaled,map_smul,smul_eq_mul]
  unfold pot
  rw [map_prod]
  simp_rw [post_change,degree _ _ (h _),map_smul]
  simp only [Algebra.smul_def,map_prod,Finset.prod_mul_distrib]

theorem invariant (a:Fin 2→ℂ)(inverse:a 0*a 1=1)(Q:Symmetric (Fin 2 × V))
    (clear:∀i j:Fin 2 × V,i.1=j.1→Q.cov i j=0):scope (edit a) Q=Q:=by
  apply Symmetric.ext
  funext i j
  rw [cov]
  by_cases where_:i.1=j.1
  · simp [clear i j where_]
  · have weights:a i.1 *a j.1=1:=by
      rcases i with ⟨i,x⟩
      rcases j with ⟨j,y⟩
      dsimp only at where_ ⊢
      fin_cases i <;> fin_cases j <;> simp_all [mul_comm]
    rw [weights,one_mul]

end YM.Integration.WilsonPhysicalThermalWickRescale
end
