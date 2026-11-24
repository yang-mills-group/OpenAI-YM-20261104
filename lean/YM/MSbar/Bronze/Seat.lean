import YM.MSbar.Bronze.Rent
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bronze
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Tensor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {σ:Type}[Fintype σ][DecidableEq σ]
local notation "H"=>Cacao.Pot σ
local notation "μ"=> PowerSeries.coeff
variable {S:Cacao.Pot σ}{G:Gauge}{c:Side}{a m k p q n r:ℕ}{b D A K L₀ α E w:ℝ}
open MvPolynomial Finset
local notation "V"=> PowerSeries ℝ
noncomputable def brim (r:ℕ)(p:PowerSeries ℝ)(X:ℝ): Prop:=∀ i≤r,|PowerSeries.coeff i p|≤X
variable (v:PowerSeries ℝ)
local notation "i₀"=>homogeneousComponent
lemma pers {l:σ→Site c}(h:Tin l α p m w S K) : Tin l α p m w (homogeneousComponent n S) K:=by
   refine ⟨h.1,fun j hj i=>?_⟩; rw [← scored]; refine le_trans ?_ ((scored S i).le.trans (h.fan j hj i)); apply shiny; intro L hh; rw [jewels]; apply mul_le_mul_of_nonneg_right _ (effect ..|>.le); split; exact le_rfl; next hh=> exact abs_zero.le.trans (abs_nonneg _)
lemma brim_pow (h:brim n v D)(d:ℕ)(hh:0 ≤ D) : brim n (v^d) (((n+1:ℕ)*D:ℝ)^d):=by
    let B:=((n+1:ℕ)*D:ℝ); have hB:0≤B:=by unfold B; positivity
    induction d with|zero=> intro i he; by_cases hx:i=0 <;> simp [hx]
                    |succ i ih=>
                       rw [pow_succ,pow_succ _ i]; intro k hk
                       rw [PowerSeries.coeff_mul]; apply (Finset.abs_sum_le_sum_abs ..).trans; refine (Finset.sum_le_sum (g:=fun _ :ℕ × ℕ=> B^i*D) ?_).trans ?_
                       · intro j hj; have he:j.1+j.2=k:=mem_antidiagonal.mp hj; rw [abs_mul]; exact mul_le_mul (ih _ (by omega)) (h _ (by omega)) (abs_nonneg _) (by positivity)
                       rw [Finset.sum_const,Nat.card_antidiagonal,nsmul_eq_mul]; change _ ≤ B^i * B; exact (mul_le_mul_of_nonneg_right (show ((k+1:ℕ):ℝ) ≤ ((n+1:ℕ):ℝ) by exact_mod_cast Nat.add_le_add_right hk 1) (by positivity : 0≤ B^i*D)).trans_eq (by ring)
noncomputable def term (r i j:ℕ)(D:ℝ):=let B:=((r+1:ℕ):ℝ); B*((B*D)^i*(B*( (1+B*D)^r))^j)
lemma cold (h:μ 0 v = 1)(hx:brim n v D)(hh:1≤D):brim n v⁻¹ ((1+(n+1:ℕ)*D:ℝ)^n):=by
    let T:= ((n+1:ℕ):ℝ); let B:= 1+T*D; have H₁:0≤ D:= zero_le_one.trans hh; have hp:1 ≤ B:= le_add_of_nonneg_right (mul_nonneg (by unfold T; positivity) H₁); have H₂:0 ≤ B:=zero_le_one.trans hp
    have hv : PowerSeries.constantCoeff v=1:=PowerSeries.coeff_zero_eq_constantCoeff_apply v |>.symm.trans h -- defeq
    have hk(i)(he:i≤n):|μ i v⁻¹|≤B^i:=by
        induction i using Nat.strong_induction_on with
        | h i ih=>
           rw [PowerSeries.coeff_inv,hv]; split
           next ht=> simp [ht]
           next ht=>
              obtain ⟨l,rfl⟩:= Nat.exists_eq_succ_of_ne_zero ht; simp only [inv_one,neg_mul,one_mul,abs_neg]; rw [pow_succ]; apply (Finset.abs_sum_le_sum_abs ..).trans ?_; let T':= B^l * D
              calc
                 _ ≤ ∑ i∈ antidiagonal (l+1),T' := by
                     refine Finset.sum_le_sum fun j hj=>?_ ; have hz:j.1+j.2=l+1:=mem_antidiagonal.mp hj; split; next h=> rw [abs_mul]; change _ ≤ B^l*D; rw [mul_comm (B^l)]; exact mul_le_mul (hx j.1 (by omega)) ((ih j.2 (by omega) (by omega)).trans (pow_le_pow_right₀ hp (by omega))) (abs_nonneg _) (zero_le_one.trans hh)
                     next hh=> rw [abs_zero]; unfold T'; positivity
                 _ ≤ _:=by
                     rw [Finset.sum_const, Nat.card_antidiagonal,nsmul_eq_mul]; refine le_trans (b:=T*(B^l*D)) ?_ ?_
                     · exact mul_le_mul_of_nonneg_right (by unfold T; exact_mod_cast Nat.add_le_add_right he 1: ((l+1+1:ℕ):ℝ) ≤ T) (by positivity)
                     rw [show T*(B^l*D)=B^l*(T*D) from by ring]; exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity)
    intro i hi; exact (hk i hi).trans (pow_le_pow_right₀ hp hi)
lemma star (i j:ℕ)(h:μ 0 v=1)(hx:brim n v D)(hp:1≤D):brim n (v^i*v⁻¹^j) (term n i j D):=by
   have hP:= brim_pow v hx i (zero_le_one.trans hp); have hQ:= brim_pow (v⁻¹) (cold v h hx hp) j (by have he:0≤D:=zero_le_one.trans hp; positivity)
   let B:=((n+1:ℕ)*D:ℝ); have he:0 ≤ B:=mul_nonneg (by positivity) (zero_le_one.trans hp); let T:= ((n+1:ℕ):ℝ); have ht:0≤ T:=by unfold T; positivity
   intro k hk; rw [PowerSeries.coeff_mul]; let γ:= (B^i*((T*( (1+B)^n))^j)); have hg:0≤γ:=by unfold γ; positivity
   apply (Finset.abs_sum_le_sum_abs ..).trans ?_; apply le_trans (b:=∑ i∈antidiagonal k,γ) (Finset.sum_le_sum ?_) ?_
   · intro l hh; have he':l.1+l.2=k:=mem_antidiagonal.mp hh; rw [abs_mul]; exact mul_le_mul (hP _ (by omega)) (hQ _ (by omega)) (abs_nonneg _) (pow_nonneg he _)
   rw [sum_const,Nat.card_antidiagonal,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by unfold T; exact_mod_cast Nat.add_le_add_right hk 1: ((k+1:ℕ):ℝ)≤ T) hg
end YM.MSbar.Bronze
