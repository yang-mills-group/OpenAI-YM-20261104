import YM.RegulatorIR.Cluster.Ward
import YM.RegulatorIR.Primitives.Verse

/-!
# Algebra for Ward lift
Substitute a power series into *coefficient labels* (through W1). Use only
if contour coefficients know Ward through pledged index. No convergence. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Ward
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Prim Finset PowerSeries
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff
variable {I J K:Type} {i e k a b r:ℕ}{S T:PowerSeries ℝ}
-- equality through finite order

def Squares (e:ℕ) (f g : PowerSeries ℝ):Prop:=∀ i,i≤e→ coeff i f=coeff i g
namespace Squares
variable {s f g t:PowerSeries ℝ}
lemma maintains (h:Squares e s f) (H:Squares e g t): Squares e (s*g) (f*t):=by
 intro i hi; rw [coeff_mul,coeff_mul];apply Finset.sum_congr rfl;intro j hj;have hv:= Finset.mem_antidiagonal.mp hj; rw [h j.1 (by omega), H j.2 (by omega)]
lemma sub (h:Squares e s f) (H:Squares e g t):Squares e (s-g) (f-t):=by intro i hi; rw [map_sub, map_sub, h i hi,H i hi]
lemma times (h:Squares (e+r) (s*X^r) (g*X^r)) : Squares e s g:=by intro i hi; specialize h (i+r) (by omega); rwa [coeff_mul_X_pow,coeff_mul_X_pow] at h
lemma left {f : PowerSeries ℝ}(hf:coeff 0 f≠0) (h:Squares e (f*t) (f*g)): Squares e t g:=by
 have hv:= maintains (show Squares e f⁻¹ f⁻¹ from fun _ _=>rfl) h
 have hh : PowerSeries.constantCoeff f≠0:=by rwa [coeff_zero_eq_constantCoeff_apply] at hf
 rwa [← mul_assoc,← mul_assoc,PowerSeries.inv_mul_cancel _ hh,one_mul,one_mul] at hv
lemma expo_near (f: PowerSeries ℝ) (x:ℕ) (h:∀ i,i < x → coeff i f=0) {n i:ℕ}(hi:i<n*x): coeff i (f^n)=0:=by
 induction n generalizing i with
 | zero=>omega
 | succ n ih=>
    rw [pow_succ, coeff_mul];apply sum_eq_zero;intro p hp; have hc:=mem_antidiagonal.mp hp
    by_cases hx:p.1<n*x
    · rw [ih hx, zero_mul]
    rw [h p.2 (by rw [add_mul,one_mul] at hi; omega),mul_zero]
lemma era (f:PowerSeries ℝ) (i:ℕ) (h:0 < i) (H:∀ n,n < i → coeff n f=0):coeff i (expo f)= coeff i f:=by
 rw [expo,coeff_mk,truncP,map_sum,sum_eq_single_of_mem 1 (by simp [h])]; simp
 intro n _ he; rw [coeff_smul]; cases n with
 | zero=>rw [pow_zero,coeff_one,if_neg h.ne',smul_zero]
 | succ n=>
    have ht:1≤ n:=by omega
    rw [expo_near f i H (by nlinarith), smul_zero]
lemma script_inject (ht:coeff 0 t=0) (hs: coeff 0 s=0) (h : Squares e (expo t) (expo s)): Squares e t s:=by
 let f:=s-t;have hf:coeff 0 f=0:= by unfold f; rw [map_sub,hs,ht,sub_self]
 have hh:Squares e (expo f) 1:= by
    apply left (f:=expo t) (by rw [exp_start];exact one_ne_zero); rw [mul_one,← timble_exp ht hf,show t+f=s by unfold f;abel]; exact fun i hi=> (h i hi).symm
 have hx: Squares e f 0:=by
    intro i; induction i using Nat.strong_induction_on with
    | _ i ih=>
       intro hp;by_cases hk:i=0
       · subst i;rw [hf,map_zero]
       rw [← era f i (Nat.pos_iff_ne_zero.mpr hk) (fun n hn=> (ih n hn (by omega)).trans (map_zero _)), hh i hp, coeff_one,if_neg hk,map_zero]
 intro i hi;exact Eq.symm (sub_eq_zero.mp (by rw [← map_sub,show _=coeff i 0 from hx i hi,map_zero]))
end Squares

-- substitute on the coefficient algebra
section Stream
variable {R:Type}[CommRing R] (τ : R →+* ℝ⟦X⟧)
-- reuse sieve_product? private; make public in cluster Ward to reuse. yes.

noncomputable def passage (f:R⟦X⟧):ℝ⟦X⟧ := PowerSeries.mk (fun i=>coeff i (Cluster.sieve τ f i))
lemma flows {p:R⟦X⟧}(k:ℕ) (h:i≤k) : coeff i (passage τ p)=coeff i (Cluster.sieve τ p k) :=by rw [passage, coeff_mk,Cluster.sieve_cost τ p (le_refl i),Cluster.sieve_cost τ p h]
lemma flows_v (p:R⟦X⟧) (e): coeff e (passage τ p)= ∑ v∈antidiagonal e, coeff v.2 (τ (coeff v.1 p)):=by rw [flows τ _ (le_refl e),sieve_cost τ p (le_refl e)]

def tide : R⟦X⟧ →+* ℝ⟦X⟧ where
 toFun:=passage τ
 map_add' s t:=by ext i; rw [map_add, flows_v,flows_v,flows_v];simp_rw [map_add,sum_add_distrib]
 map_zero' :=by ext;simp [flows_v]
 map_mul' s t:=by
    ext1 i; rw [flows τ _ le_rfl,Cluster.sieve_product,coeff_mul,coeff_mul]; apply sum_congr rfl;intro p hp; have hz:=mem_antidiagonal.mp hp;rw [flows τ _ (show p.1≤ i by omega),flows τ _ (show p.2 ≤ i by omega)]
 map_one' :=by
    ext1 i; rw [flows_v]; by_cases h:i=0
    · subst i; simp
    rw [coeff_one, if_neg h]; apply Finset.sum_eq_zero;intro j hj; have hz:= mem_antidiagonal.mp hj; simp only [coeff_one]; split <;> rename_i hx
    · rw [map_one,coeff_one,if_neg (by omega)]
    rw [map_zero,map_zero]

lemma tide_C (x:R): tide τ (PowerSeries.C x)=τ x:=by
 ext1 i; change coeff i (passage τ _) = _; rw [show coeff i _= _ from flows_v τ _ i,sum_eq_single_of_mem (0,i) (by simp)]; simp
 intro x _ H; rw [coeff_C]; split <;> rename_i hc
 · exfalso; apply H; have hz:= mem_antidiagonal.mp (by assumption : x∈antidiagonal i); exact Prod.ext hc (show x.2=i by omega)
 rw [map_zero,map_zero]
lemma tide_X : tide τ (PowerSeries.X)=PowerSeries.X:=by
 ext1 i; change coeff i (passage τ _) = _; rw [show _=_ from flows_v τ (PowerSeries.X) i]; by_cases h:i=1
 · subst i; rw [show antidiagonal (1:ℕ)={(1,0),(0,1)} by decide]; simp
 rw [coeff_X, if_neg h]; apply Finset.sum_eq_zero; intro j hj; have hz:=mem_antidiagonal.mp hj; rw [coeff_X]; split <;> rename_i hx
 · rw [map_one, coeff_one, if_neg (by omega)]
 rw [map_zero,map_zero]
end Stream

section Alg
variable {R:Type}[CommRing R][Algebra ℝ R] (τ : R →ₐ[ℝ] ℝ⟦X⟧)

-- scalar algebra

def ocean : R⟦X⟧ →ₐ[ℝ] ℝ⟦X⟧ := AlgHom.mk' (tide τ.toRingHom) (by intro a b; rw [Algebra.smul_def,PowerSeries.algebraMap_apply,map_mul,tide_C]; rw [Algebra.smul_def]; exact congr_arg (· *_) (τ.commutes a))
lemma submerge (f:R⟦X⟧) (i:ℕ) : coeff i (ocean τ f)=∑ v∈antidiagonal i,coeff v.2 (τ (coeff v.1 f)):= flows_v ..
lemma ocean_const (p:PowerSeries ℝ) : ocean τ (PowerSeries.map (algebraMap ℝ R) p)=p:=by
 ext i; rw [submerge]; simp_rw [coeff_map, τ.commutes]; rw [Finset.sum_eq_single_of_mem (i,0) (by simp)]; simp
 intro j _ h; have hx:=mem_antidiagonal.mp (by assumption : j∈antidiagonal i); rw [show algebraMap ℝ (PowerSeries ℝ)= _ from PowerSeries.algebraMap_eq,coeff_C, if_neg]; exact fun hg=> h (Prod.ext (by change j.1=i; omega) hg)
lemma solar (f:R⟦X⟧) (h:coeff 0 f=0) : ocean τ (expo f)=expo (ocean τ f):=by
 have hx (i) : ocean τ (truncP f i)= truncP (ocean τ f) i:=by simp_rw [truncP,map_sum,map_smul,map_pow]
 have he: coeff 0 (ocean τ f)=0:=by rw [submerge]; simp [h]
 ext1 i;rw [expo_any he (le_refl i),← hx]; rw [submerge,submerge]; apply Finset.sum_congr rfl;intro j hj;rw [expo_any h (show j.1 ≤ i by have hx:=mem_antidiagonal.mp hj;omega)]
end Alg
end YM.RegulatorIR.Ward
