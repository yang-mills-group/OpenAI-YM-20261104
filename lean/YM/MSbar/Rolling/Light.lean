import YM.MSbar.Rolling.Stays
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Rolling
open Function Filter MeasureTheory Set Cacao Price Bakery Portal
open scoped Topology Classical BigOperators ContDiff
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
variable {σ ι ψ:Type} [Fintype σ][Fintype ι]{p n:ℕ}
local notation "Q"=>View σ
local notation "H"=>View ι
local notation "P"=>PowerSeries (Pot σ)
local notation "µ"=> PowerSeries.coeff
open Matrix MvPolynomial
noncomputable def rail (L:Matrix ι σ ℝ) : (Pot ι)→ₐ[ℝ] (Pot σ) := aeval fun i:ι=> ∑ j,MvPolynomial.C (L i j)*MvPolynomial.X j
lemma clearL (L:Matrix ι σ ℝ) (x: Q) : MvPolynomial.eval x ∘ rail L=⇑(MvPolynomial.eval (L *ᵥ x)):=by
    funext u; change eval x (rail L u)=_; induction u using MvPolynomial.induction_on with
    | C a => simp [rail]
    | add p q hp hq=> simp only [_root_.map_add,hp,hq]
    | mul_X p i hp=> simp only [_root_.map_mul,hp]; simp only [_root_.map_mul, rail, aeval_X,_root_.map_sum,eval_C,eval_X];rfl
lemma clearD (L:Matrix ι σ ℝ)(u:Pot ι) : (rail L u).totalDegree ≤ u.totalDegree:=by
   let A:=rail L; have hf(i:ι):(A (MvPolynomial.X i)).totalDegree ≤ 1:=by
        simp only [A,rail,aeval_X]; refine totalDegree_finsetSum_le (fun j _=>?_); refine (totalDegree_mul ..).trans_eq (by rw [totalDegree_C,totalDegree_X])
   nth_rw 1 [MvPolynomial.as_sum u]; rw [_root_.map_sum]; apply totalDegree_finsetSum_le; intro i hi; rw [monomial_eq]; change (A _).totalDegree ≤ _; rw [_root_.map_mul,_root_.map_finsuppProd] -- map prod
   refine (totalDegree_mul ..).trans ?_; simp only [Finsupp.prod]
   simp only [A,rail,MvPolynomial.aeval_C]
   rw [show algebraMap ℝ (Pot σ)= C from rfl,totalDegree_C,Nat.zero_add]
   refine (totalDegree_finsetProd ..).trans <| le_trans ?_ (le_totalDegree hi)
   apply Finset.sum_le_sum; intro j hj; change totalDegree (A (_ ^ _))≤ i j; rw [_root_.map_pow]; have ht:= hf j; refine (totalDegree_pow ..).trans ?_; exact (Nat.mul_le_mul_left (i j) ht).trans_eq (Nat.mul_one _)
variable {X:ℝ→ψ→Prop}{L:Matrix ι σ ℝ}{w:ℝ→ψ→View σ}
lemma ClearMain (T:PowerSeries (Pot ι))(x:View σ)(p:ℕ)(z:ℝ):taste p (picture x (PowerSeries.map (rail L).toRingHom T)) z=taste p (picture (L *ᵥ x) T) z:=by
    unfold taste picture; apply Finset.sum_congr rfl; intro i _; rw [PowerSeries.coeff_map,PowerSeries.coeff_map,PowerSeries.coeff_map]; exact congr_arg _ (congr_fun (clearL L x) (µ i T))
lemma rollQ (t:ℕ){z:ℝ→ψ→ℝ}(h:Price X (n+t) z): Price X n (fun x y=> z x y/x^t):=by
    obtain ⟨a,h⟩:=h; refine ⟨a,?_⟩; filter_upwards [width,h] with x ⟨hu,he,hx⟩ hh y hy; rw [norm_div,norm_pow,Real.norm_of_nonneg hu.le,div_le_iff₀ (pow_pos hu t)]; refine (hh y hy).trans_eq ?_; ring
lemma lens (k p:ℕ)(f:View σ→ℝ) (h:∀ i:ℕ,i<k → ∀ z,Tensor.diagonal (Tensor.coeff f i 0) z=0) (x:ℝ)(v:View σ):taste (k+p) (picture v (singularity f 0)) x=x^k*taste p (picture v (singularity f k)) x:=by
   unfold taste; rw [add_assoc,Finset.sum_range_add,Finset.mul_sum,Finset.sum_eq_zero,zero_add]; swap
   · intro i hi; simp only [picture,singularity,PowerSeries.coeff_map,PowerSeries.coeff_mk]; rw [pots,Nat.add_zero,h i (Finset.mem_range.mp hi),mul_zero] -- k+p parse
   apply Finset.sum_congr rfl; intro i hi; simp only [picture,singularity,PowerSeries.coeff_map,PowerSeries.coeff_mk]; rw [Nat.add_zero,Nat.add_comm i k,pow_add,mul_assoc]; -- Nat.add_zero target check
lemma earn (k n:ℕ)(f:View σ→ℝ)(hf:ContDiffAt ℝ ω f 0) (h:∀ i:ℕ,i<k → ∀ z,Tensor.diagonal (Tensor.coeff f i 0) z=0) (x:ℝ→ψ→View σ)(he:Price X 0 x):Price X (n+1) (fun t y => f (t•x t y)/t^k - taste n (picture (x t y) (singularity f k)) t):=by
    have ht:= prop f x (k+n) he (hf.of_le le_top); have hv:k+n+1=n+1+k:=by omega
    refine ((rollQ k (n:=n+1) (z:=fun t y=> f (t • x t y)-taste (k+n) (picture (x t y) (singularity f 0)) t) ?_)).egress ?_
    · rw [← hv]; exact ht
    filter_upwards [width] with x' hX y _; rw [lens ..]; field_simp [(hX.1).ne']; exact h -- syntax
noncomputable def splitV (v:P):P:= v - PowerSeries.C (µ 0 v)
lemma splitK (v:P) : Kind (splitV v):=by simp [Kind, splitV]
lemma SplitT (v:P)(x:Q)(t:ℝ)(p:ℕ):taste p (picture x v) t= taste p (picture x (splitV v)) t+ MvPolynomial.eval x (PowerSeries.coeff 0 v):=by
    have he:v= splitV v + PowerSeries.C (µ 0 v):=by simp [splitV]
    nth_rw 1 [he]; rw [picture,map_add,taste_add]; refine congr_arg _ ?_; unfold taste; rw [Finset.sum_range_succ']; simp -- C
end YM.MSbar.Rolling
