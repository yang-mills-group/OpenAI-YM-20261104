import YM.MSbar.Cacao.Stock
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Cacao
open PowerSeries Finset Function Polynomial
open scoped BigOperators Classical
variable {σ : Type}[Fintype σ][DecidableEq σ]
open MvPolynomial
local notation "P"=> Pot σ
local notation "B"=> Ball σ
variable (k : σ→σ→ℝ) (p:Pot σ)
local notation "L"=> stove k
noncomputable def tureen (k:σ→σ→ℝ) (c:σ) := ∑ i,k c i • ((pderiv (R:=ℝ) i).toLinearMap)
local notation "J"=> tureen k
lemma drink (i:σ) (p:Pot σ): tureen k i p=∑ j, k i j • pderiv j p:= by unfold tureen; simp
lemma lever (i:σ): L (pderiv i p)=pderiv i (L p) := by rw [stokes,stokes]; simp only [_root_.map_sum]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro j _; rw [seasoning j i,seasoning a i,Derivation.map_smul]
lemma turning (i:σ): L ((tureen k i) p)= (tureen k i) (L p):=by simp_rw [drink,_root_.map_sum,map_smul,lever k]
lemma magnet (i:σ)(h:∀ a b,k a b=k b a): L (p* MvPolynomial.X i) = (L p)*MvPolynomial.X i + (tureen k i) p:=by
   rw [stokes,stokes]; let v (a b:σ): ℝ:= k a b/2
   have he(a b:σ): pderiv a (pderiv b (p * MvPolynomial.X i)) = pderiv a (pderiv b p)*MvPolynomial.X i + ((if a=i then pderiv b p else 0)+(if b=i then pderiv a p else 0)):= by
       by_cases hx:a=i<;> by_cases hz:b=i<;> simp only [pderiv_mul] -- repeat
       all_goals simp [hx,hz,pderiv_mul,Ne.symm,eq_comm] <;> ring
   rw [Finset.sum_mul]; simp_rw [he,smul_add,Finset.sum_add_distrib,Finset.sum_mul,smul_mul_assoc]
   let D(i):= pderiv i p; have hx(a): pderiv a p=(pderiv a p):=rfl
   apply congr_arg; rw [sum_comm]; simp only [smul_ite,smul_zero, Finset.sum_ite_eq', mem_univ, ↓reduceIte]; rw [drink, ← sum_add_distrib]; refine sum_congr rfl (fun j _=>?_); rw [h j i, ← add_smul,add_halves]
-- commute powers simplify into pour recursion
lemma gradient (m:ℕ)(i:σ): (L^m) ((tureen k i) p)= (tureen k i) ((L^m) p):=by
   induction m with
   | zero=> simp only [pow_zero]; rfl
   | succ j ih=> rw [pow_succ']; change L (((L)^j) ((J i) p))=(J i) (L (((L)^j) p)); rw [ih,turning]
lemma chargeP (i:σ)(h:∀ a b,k a b=k b a)(m:ℕ): (L^(m+1)) (p*MvPolynomial.X i)=((L^(m+1)) p)*MvPolynomial.X i + ((m+1:ℝ)) • ((tureen k i) ((L^m) p)):=by
   induction m with
   | zero=> simpa using magnet k p i h
   | succ j ih=> rw [pow_succ' _ (j+1)]; change L (((L^(j+1)) (p*_)))= L (_)*_ + _; rw [ih,_root_.map_add,_root_.map_smul,turning,magnet k _ i h]; push_cast; have h' : (L^(j+1)) p=L ((L^j) p) :=by rw [pow_succ'];rfl
                 rw [h']; simp only [add_smul,one_smul]; abel
lemma drinkPower (i:σ)(h:∀ a b,k a b=k b a)(n:ℕ): (pearl k (p*MvPolynomial.X i)).coeff (n+1) = (pearl k p).coeff (n+1)* (MvPolynomial.X i)+tureen k i ((pearl k p).coeff n):=by
    simp_rw [season,pour]; rw [chargeP k p i h,smul_add,_root_.map_smul, ← smul_mul_assoc, smul_smul, from_1 (0:ℝ→ₗ[ℝ]ℝ) (by simp) n]
-- polynomial τ at 1
noncomputable def bowl (k:σ→σ→ℝ)(p:Pot σ):P:= Polynomial.eval 1 (pearl k p)
lemma sip (F:Ball σ)(j:ℕ) (h: F.natDegree ≤ j) : Polynomial.eval 1 F = ∑ i∈Finset.range (j+1),F.coeff i :=by
   rw [Polynomial.eval_eq_sum_range' (by omega : F.natDegree<j+1)]; simp -- name
lemma slipE (D: Module.End ℝ P)(F:Ball σ) : Polynomial.eval 1 (elevatorP D F)= D (Polynomial.eval 1 F):=by
    let k:= max F.natDegree (elevatorP D F).natDegree; rw [sip _ k (le_max_right ..),sip _ k (le_max_left ..),_root_.map_sum]; exact sum_congr rfl fun i _=> riseP ..
lemma spout (i:σ)(h:∀ a b,k a b=k b a): bowl k (p*MvPolynomial.X i) = bowl k p * MvPolynomial.X i + (tureen k i) (bowl k p):=by
    let f:=elevatorP (tureen k i) (pearl k p); have hp: pearl k (p*MvPolynomial.X i)= pearl k p* Polynomial.C (MvPolynomial.X i) + f * Polynomial.X := by
        apply Polynomial.ext; intro n; cases n with | zero=>rw [winter];simp [winter k]| succ n=> rw [drinkPower k p i h, Polynomial.coeff_add]; simp only [Polynomial.coeff_mul_C, Polynomial.coeff_mul_X, Nat.add_one_sub_one]; rw [show f.coeff n= _ from riseP ..] -- ambiguity
    unfold bowl; rw [hp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X, mul_one,show Polynomial.eval 1 f=_ from slipE (tureen k i) _]
end YM.MSbar.Cacao
