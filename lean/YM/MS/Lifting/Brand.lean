import YM.MS.Color.Mean

set_option autoImplicit false
noncomputable section
namespace YM.MS.Lifting
open Function Filter Set Finset Plane Koszul Color Real Momentum Tensor
open Local Local.BV Landau Detect Detect.Mark MeasureTheory
open Complex (I)
open scoped Topology ContDiff BigOperators
variable {G:Gauge} {n:ℕ}
abbrev Grid (G:Gauge)(n:ℕ):= Fin n→CI G
def ink (c:G.El)(r s: Grid G n):ℝ := ∏ i, weight c (r i) (s i)
def group (G:Gauge) (i j:Grid G n):ℝ:= ∫ u, ink u i j ∂G.probHaar
lemma massInk (i j:Grid G n): Integrable (fun u=>ink u i j) G.probHaar:= (continuous_finsetProd _ (fun x _=> (show Continuous (fun u:G.El=> weight u (i x) (j x)) by simpa [wc,Function.comp_def] using Complex.continuous_re.comp (weight_cont (i x) (j x))))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
variable {E R : Type*} [CommRing R][Algebra ℝ R][AddCommGroup E][Module R E] -- R=ℂ ℝ generic
variable (R)
lemma all_add (n:ℕ) (f: Grid G (n+1)→E): ∑ k:Grid G (n+1), f k =∑ i:CI G,∑ q:Grid G n, f (Fin.cons i q):= by rw [← Equiv.sum_comp (Fin.consEquiv _) f,Fintype.sum_prod_type]; rfl
def prodS (prod:E→ₗ[R] E→ₗ[R] E)(e:E): (k:ℕ)→(Fin k→E)→E | 0,_=> e| k+1, t=> prod (t 0) (prodS prod e k (t∘Fin.succ))
variable {R}
lemma color_expand (prod:E→ₗ[R] E→ₗ[R] E)(e:E)(n:ℕ)(u:Fin n→ CI G→ E)(c:G.El)(i:Grid G n):
    prodS R prod e n (fun j=> ∑ k:CI G, algebraMap ℝ R (weight c k (i j)) • u j k)= ∑ k:Grid G n, algebraMap ℝ R (ink c k i) • prodS R prod e n (fun j=>u j (k j)):= by
   induction n with
   | zero=>
       have hx : Fintype.card (Grid G 0)=1:= by simp [Grid]
       simp [prodS,ink]
   | succ n ih=> rw [prodS, map_sum,all_add]; rw [LinearMap.sum_apply]; refine Finset.sum_congr rfl (fun j _=>?_); simp only [Function.comp_def, ih (fun j=>u j.succ) (fun j=> i j.succ), ink,Fin.prod_univ_succ, Fin.cons_zero,Fin.cons_succ,prodS,map_sum,map_smul, LinearMap.smul_apply, map_mul,mul_smul]; exact Finset.sum_congr rfl (fun i _=> smul_comm ..)
omit [Algebra ℝ R] in
lemma prod_color (P:E→ₗ[R] E)(prod:E→ₗ[R] E→ₗ[R] E)(e:E)(n:ℕ)(u:Fin n→E)(h:P e=e)(he:∀ i j, P (prod i j)= prod (P i) (P j)): P (prodS R prod e n u)=prodS R prod e n (P∘u):= by
   induction n with
   | zero=> exact h
   | succ n ih=> rw [prodS, he, ih]; rfl
end YM.MS.Lifting
