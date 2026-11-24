import YM.SchemeConversionRG11.FirstW.Invoice.Each
/-! Gaussian open-extras recursion. No distinct-mark shortcut. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option autoImplicit false
namespace YM.RG11.FirstW.Deck
open Function Filter MeasureTheory ProbabilityTheory Set Lattice Pert Warp Topology Maxwell
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsGaussian μ] {I : Type*} [Fintype I] [DecidableEq I]
abbrev Cache (I : Type*) := MvPolynomial I ℂ
variable (t : I → Query E)
-- evaluation convention
noncomputable def spend (p : Cache I) := fun x=> MvPolynomial.eval (fun i:I=> t i x) p
lemma spend_A (p : Cache I) : Orb.Tame (spend t p) := by
  induction p using MvPolynomial.induction_on with
  | C c=>unfold spend;simp only [MvPolynomial.eval_C]; exact Orb.Tame.constant _
  | add p q h k=> unfold spend;simp only [map_add]; exact Orb.Tame.add h k
  | mul_X p i h=> unfold spend;simp only [map_mul, MvPolynomial.eval_X]; exact Orb.Tame.mul h (Orb.Tame.clm (t i))
variable (Y : Query E)
def extra (p : Cache I) (L : ℕ→Query E) (s : Finset ℕ) (x : E) := (∏ a∈s,L a x)*spend t p x
lemma extra_tame (p : Cache I) (L : ℕ→Query E) (s : Finset ℕ) : Orb.Tame (extra t p L s) := by
  have he : Orb.Tame (fun x=> ∏ a ∈ s,L a x) := by
    induction s using Finset.induction_on with
    | empty=> simp only [Finset.prod_empty]; exact Orb.Tame.constant _
    | insert i S h ih=> simp only [Finset.prod_insert h]; exact Orb.Tame.mul (Orb.Tame.clm _) ih
  exact Orb.Tame.mul he (spend_A t p)
lemma extra_cost (p : Cache I) (L : ℕ→Query E) (s : Finset ℕ) : Integrable (extra t p L s) μ := price_tame μ (extra_tame t p L s)
def refundC (L : ℕ→Query E) (s : Finset ℕ) (p : Cache I) := ∑ a∈s,coins μ Y (L a) * ∫ x,extra t p L (s.erase a) x ∂μ
lemma pen_X (i : I) (k : ℕ) (L : ℕ→Query E) (p : Cache I) (s : Finset ℕ) (hk:k∉s) (x : E) : extra t p (Function.update L k (t i)) (insert k s) x=extra t (p*MvPolynomial.X i) L s x := by
  unfold extra; rw [Finset.prod_insert hk, Function.update_self, Finset.prod_congr (s₂:=s) rfl (g:=fun j=>L j x) (fun j hj=> by rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hk)])]; simp only [spend,map_mul,MvPolynomial.eval_X]; ring
lemma after_fee (i : I) (k : ℕ) (L : ℕ→Query E) (p : Cache I) (s : Finset ℕ) (hk:k∉s) :
    refundC μ t Y (Function.update L k (t i)) (insert k s) p = coins μ Y (t i) * (∫ x,extra t p L s x ∂μ) + refundC μ t Y L s (p*MvPolynomial.X i) := by
  rw [refundC,Finset.sum_insert hk,Function.update_self,Finset.erase_insert hk,refundC]; congr 1
  · apply congrArg _; apply congrArg (fun f:E→ℂ=>∫ x,f x ∂μ); funext x; unfold extra; refine congrArg (· * _) (Finset.prod_congr rfl fun j hj=>?_); rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hk)]
  refine Finset.sum_congr rfl fun a ha=>?_; have eh := ne_of_mem_of_not_mem ha hk
  rw [Function.update_of_ne eh,Finset.erase_insert_of_ne (Ne.symm eh)]; apply congrArg _; exact congrArg (fun f:E→ℂ=> ∫ x,f x ∂μ) (funext (pen_X t i k L p (s.erase a) (fun hh=>hk (Finset.mem_of_mem_erase hh))))
def priceD (L : ℕ→Query E) (s : Finset ℕ) (p : Cache I) := ∑ a:I,coins μ Y (t a) * ∫ x,extra t (MvPolynomial.pderiv a p) L s x ∂μ
lemma extra_plus (p q : Cache I) (L : ℕ→Query E) (s : Finset ℕ) : extra t (p+q) L s = extra t p L s + extra t q L s := funext (fun x=>by simp [extra,spend,mul_add])
lemma priceD_X (i : I) (k : ℕ) (L : ℕ→Query E) (p : Cache I) (s : Finset ℕ) (hk:k∉s) :
    priceD μ t Y L s (p* MvPolynomial.X i)= priceD μ t Y (Function.update L k (t i)) (insert k s) p + coins μ Y (t i)*(∫ x,extra t p L s x ∂μ) := by
  unfold priceD
  let M a := coins μ Y (t a)*(∫ x,extra t (MvPolynomial.pderiv a (p*MvPolynomial.X i)) L s x ∂μ)
  let P a := coins μ Y (t a)*(∫ x,extra t (MvPolynomial.pderiv a p) (Function.update L k (t i)) (insert k s) x ∂μ)
  have hd (a : I) : ∫ x,extra t (MvPolynomial.pderiv a p * MvPolynomial.X i) L s x ∂μ = ∫ x,extra t (MvPolynomial.pderiv a p) (Function.update L k (t i)) (insert k s) x ∂μ := congrArg (fun f:E→ℂ=>∫ x,f x ∂μ) (funext (pen_X t i k L _ _ hk)).symm
  have he (a : I) : M a = P a + (if i=a then coins μ Y (t i)*(∫ x,extra t p L s x ∂μ) else 0) := by
    unfold M P
    by_cases H:i=a
    · subst a; have eh : MvPolynomial.pderiv i (p* MvPolynomial.X i)= p+(MvPolynomial.pderiv i p)*MvPolynomial.X i := by simp [mul_comm (MvPolynomial.X i)] -- already closed
      simp only [if_true,eh,extra_plus,Pi.add_apply]; rw [integral_add (extra_cost ..) (extra_cost ..),hd]; ring
    have eh : MvPolynomial.pderiv a (p*MvPolynomial.X i)= MvPolynomial.pderiv a p*MvPolynomial.X i := by simp [H,mul_comm (MvPolynomial.X i)] -- name
    rw [eh, if_neg H,hd,add_zero]
  change ∑ a,M a=(∑ a,P a)+_; simp only [he,Finset.sum_add_distrib]; congr 1; simp
lemma price_sum_linear (A : E→ℂ) (hA : Orb.Tame A) (L : ℕ→Query E) (s : Finset ℕ) (p q : Cache I) : (∫ x,A x*extra t (p+q) L s x ∂μ) = (∫ x,A x*extra t p L s x ∂μ) + ∫ x,A x*extra t q L s x ∂μ := by rw [extra_plus]; simp only [Pi.add_apply,mul_add]; exact integral_add (price_tame μ (Orb.Tame.mul hA (extra_tame ..))) (price_tame μ (Orb.Tame.mul hA (extra_tame ..)))
lemma takeoff (h : ∀ i,Laugh μ (t i)) (hY : Laugh μ Y) (p : Cache I) : ∀ (L : ℕ→Query E) (s : Finset ℕ), (∀ k,Laugh μ (L k)) →
    (∫ x,Y x * extra t p L s x ∂μ) = refundC μ t Y L s p + priceD μ t Y L s p := by
  induction p using MvPolynomial.induction_on with
  | C c=>
    intro L s H
    simp only [extra,spend, MvPolynomial.eval_C, ←mul_assoc]; rw [integral_mul_const, term_add μ L Y s hY H]; unfold refundC priceD; simp only [extra,spend,MvPolynomial.eval_C, MvPolynomial.pderiv_C,map_zero,mul_zero,integral_zero, Finset.sum_const_zero,add_zero, team]; simp only [integral_mul_const, Finset.sum_mul,mul_assoc]
  | add p q ih jh=>
    intro L s H; rw [price_sum_linear μ t _ (Orb.Tame.clm Y), ih L s H, jh L s H]; simp only [refundC,priceD, map_add,extra_plus,Pi.add_apply,integral_add (extra_cost ..) (extra_cost ..),mul_add, Finset.sum_add_distrib]; abel
  | mul_X p i ih=>
    intro L s H; obtain ⟨z,hz⟩:=Infinite.exists_notMem_finset s; let a:=update L z (t i)
    have hg (k:ℕ): Laugh μ (a k) := by
      by_cases hx:k=z
      · rw [hx]; unfold a; rw [update_self]; exact h i
      unfold a; rw [update_of_ne hx]; exact H k
    have he:=ih a (insert z s) hg; unfold a at he; rw [after_fee μ t Y i z L p s hz] at he; simp only [pen_X t i z L p s hz] at he; rw [he,priceD_X μ t Y i z L p s hz]; abel
end YM.RG11.FirstW.Deck
