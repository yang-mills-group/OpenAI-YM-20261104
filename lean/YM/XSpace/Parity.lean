import YM.XSpace.Grow
import YM.XSpace.Reversal
/-!
# Slot parity J0 on Wick labels and all determining data
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Taylor
open Next.Rank.Normal MvPolynomial Maxwell Maxwell.Free
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {σ τ:Type*} {n:ℕ}
lemma bulk_sign (s:σ →₀ ℕ) (x:ℂ):
    mirror σ (MvPolynomial.monomial s x)= ((-1:ℂ)^(Finsupp.weight (fun _:σ=> (1:ℕ)) s)) • MvPolynomial.monomial s x:=by
  induction s using Finsupp.induction with
  | zero=> simp [mirror]
  | single_add i m s hi hm ih=>
    have hv : MvPolynomial.monomial (Finsupp.single i m+s) x=X i^m * MvPolynomial.monomial s x:=by rw [X_pow_eq_monomial,monomial_mul,one_mul]
    rw [hv,map_mul,map_pow,ih,mirror,aeval_X]; simp only [_root_.map_add,Finsupp.weight_single,smul_eq_mul,mul_one, mul_smul_comm]
    rw [← neg_one_mul (X (R:=ℂ) i),mul_pow,pow_add]; rw [← C_mul',← C_mul',map_mul,map_pow,map_pow,map_neg,map_one]; ring
lemma parity_sign (p:WickPol G) (hp:Pure n p): mirror _ p=((-1:ℂ)^n) • p:= by
  rw [MvPolynomial.as_sum p]; simp_rw [_root_.map_sum,Finset.smul_sum]; apply Finset.sum_congr rfl; intro i hi; rw [bulk_sign,hp (MvPolynomial.mem_support_iff.mp hi)]
lemma reflections (p : Pol σ): mirror _ (mirror _ p)=p:= by
  suffices h:(mirror σ).comp (mirror σ)=AlgHom.id ℂ _ from AlgHom.congr_fun h p; ext1 i; simp [mirror]
lemma renamed_mirror (p:Pol σ) (f:σ→τ): rename f (mirror _ p)=mirror _ (rename f p):=by
  suffices h:(rename f).comp (mirror _)= (mirror _).comp (rename f) from AlgHom.congr_fun h p; ext1 i; simp [mirror]
lemma begets {M: Type*} [AddCommMonoid M] (f:σ→M) (i:σ): IsWeightedHomogeneous f (mirror σ (X i)) (f i):=by
  rw [mirror,aeval_X]; exact (MvPolynomial.weightedHomogeneousSubmodule ℂ f (f i)).neg_mem (isWeightedHomogeneous_X ..)
lemma mirror_sym (l:ℕ) (p: Probe G l): mirror _ (symbol l p) = -symbol _ p:=by rw [parity_sign _ (show Pure 1 _ from symbol_hom p (fun _=> (1:ℕ))),pow_one,neg_one_smul]
lemma mirrored (s:Ortho) (p : WickPol G): mirror _ (reflectPol s p)= reflectPol s (mirror _ p):=by
  suffices h: (mirror _).comp (reflectPol (G:=G) s)=(reflectPol s).comp (mirror _) from AlgHom.congr_fun h p; ext1 i; simp only [AlgHom.comp_apply,reflectPol,aeval_X,mirror_sym, show mirror (Slot G) (X i)=- X i from aeval_X ..,map_neg]
lemma mirror_color (u:G.El) (p:WickPol G): mirror _ (pigment u p)= pigment u (mirror _ p):=by
  suffices h:(mirror _).comp (pigment u)= (pigment u).comp (mirror _) from AlgHom.congr_fun h p; ext1 i; simp only [AlgHom.comp_apply,pigment,aeval_X,mirror_sym, show mirror (Slot G) (X i)=- X i from aeval_X ..,map_neg]
lemma mirror_real (p:WickPol G): mirror _ (realForm p)=realForm (mirror _ p):=by
  induction p using MvPolynomial.induction_on with
  | C a => simp [mirror,realForm]
  | add p q hp hq=> simp_rw [map_add,hp,hq]
  | mul_X p i hp=> rw [map_mul,map_mul,hp,map_mul,map_mul]; simp [realForm,mirror]
lemma glossy {M:Type*} [AddCommMonoid M] (f:σ→M) (k:M) (p : Pol σ): weightedHomogeneousComponent f k (mirror _ p)=mirror _ (weightedHomogeneousComponent f k p):= commuting _ _ _ (begets f) p k
end YM.XSpace.Taylor

namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick MeasureTheory Taylor
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d n:ℕ} {E:Type} [AddCommMonoid E] [Module ℂ E]
lemma mirror_ok (p:WickPol G) (h:p∈shellSector G d): mirror _ p∈ shellSector G d := sector.mpr
  ⟨transfers _ _ _ (begets scaleW) _ (sector.mp h).1,fun u=> (mirror_color ..).symm.trans (congr_arg _ ((sector.mp h).2 u))⟩

def hinge (d:ℕ) : FieldEnd G d:= LinearMap.codRestrict _ ((mirror _).toLinearMap ∘ₗ coeS d) (fun p=> mirror_ok p.val p.property)
lemma val_hinge (p:Sec G d): (hinge d p).val=mirror _ p.val:=rfl
lemma hinges_back (p:Sec G d): hinge d (hinge d p)=p:= Subtype.ext (reflections p.val)
lemma hinge_leaf (d:ℕ) (G:Gauge): hinge d (leaf G d)= leaf G d:=Subtype.ext (show mirror _ (1:WickPol G)=1 from map_one _)
lemma hinge_ori (s:Ortho) (p:Sec G d): hinge d (ori s d p)=ori s d (hinge d p):=Subtype.ext (mirrored s _)
lemma hinge_reel (p:Sec G d): hinge d (reel d p)=reel d (hinge d p):=Subtype.ext (mirror_real _)
lemma hinge_up (h:n≤d) (p:Sec G n): hinge d (up h p)=up h (hinge n p):=rfl
lemma hinge_part (p:Sec G d) (n:ℕ): (part d n (hinge d p)).val=mirror _ (part d n p).val:= glossy ..
lemma prey (p:Sec G (d+1)): hinge d (prev d p)=prev d (hinge (d+1) p):=by unfold prev; rw [LinearMap.sum_apply,LinearMap.sum_apply,map_sum]; exact Finset.sum_congr rfl fun i _=> Subtype.ext (hinge_part p i).symm

private lemma hingeable (T:Change G d): hinge d ∘ₗ T.val ∘ₗ hinge d∈ Change G d:=by
  simp only [may_change,LinearMap.comp_apply]; exact ⟨by rw [hinge_leaf,T.property.1,map_zero],fun l hl p h=> mirror_ok _ (T.property.2.1 l hl _ (mirror_ok _ h)),fun p=> by rw [hinge_reel,T.property.2.2.1,hinge_reel],fun s p=> by rw [hinge_ori,T.property.2.2.2,hinge_ori]⟩

def arch (d:ℕ): Module.End ℝ ↥(Change G d) where
  toFun T:=⟨_,hingeable T⟩
  map_add' T U:=by apply Subtype.ext; ext1 p; change hinge d (T.val _+U.val _)= hinge d _ + hinge d _; simp only [map_add,LinearMap.comp_apply]
  map_smul' a T:= by apply Subtype.ext; ext1 p; change hinge d (a • T.val _)= a • hinge d _; exact map_smul ((hinge d).restrictScalars ℝ) _ _
lemma arched (T:Change G d) (p:Sec G d): (arch d T).val p=hinge d (T.val (hinge d p)):=rfl
lemma arches (T:Change G d): arch d (arch d T)=T:=by apply Subtype.ext; ext1 p; rw [arched,arched,hinges_back,hinges_back]
lemma arch_fell (T:Change G (d+1)): arch d (fell d T)=fell d (arch _ T):=by apply Subtype.ext; ext1 p; rw [fell_apply,arched,arched,fell_apply, ←hinge_up,prey] -- order
lemma arch_grow (T:Change G d): arch (d+1) (grow d T)= grow d (arch d T):=by apply Subtype.ext; ext1 p; rw [arched,grows,grows,arched,← prey,hinge_up]
lemma free_symmetry (p:Fin n→ WickPol G) {x:Points n} (hx:x∈conf n): moment G x (fun i=> mirror _ (p i))=moment G x p:=by
  rw [Next.Rank.Normal.Wick_reads hx, Next.Rank.Normal.Wick_reads hx]; simp_rw [renamed_mirror,← map_prod, mirror_blend]
lemma homes (P:Correl G d E): recruit (hinge d) (recruit (hinge d) P)=P:=by ext n t v; rw [recruits,recruits]; congr 1; ext1 j; simp only [Function.comp_apply,hinges_back]
lemma heredity (d:ℕ) : recruit (hinge d) (reference G d)=reference G d :=by
  ext1 n; apply LinearMap.ext; intro t; ext1 p; rw [recruits,reflects,reflects]; exact Test.apply_eq _ (fun _ hx=> free_symmetry (fun i=>(p i).val) hx)
lemma gradient_arched (T:Change G d): recruit (hinge d) (gradient G d T)=gradient G d (arch d T):=by
  change recruit _ (varies (reference G d) T.val)=varies (reference G d) (arch d T).val; rw [← enroll (hinge d) (arch d T).val T.val _ (fun p=> ?_),heredity]; rw [arched,hinges_back]
end YM.XSpace.Normalize
