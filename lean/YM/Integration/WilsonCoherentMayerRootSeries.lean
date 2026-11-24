import YM.Integration.WilsonCoherentMayerFuelSquare

/-! Accumulate an absolutely financed signed list into one bounded-degree
polynomial. Its absolute coefficient bill is the original list expense,
independently of the number of variables of the particular forest. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerRootSeries
open Finset Function MeasureTheory RG Next.Rank AnalyticBridge.LocalGaussianLaws
open scoped BigOperators Classical
variable {E:Type*} [Fintype E]

private def stock (E:Type*) [Fintype E](k:ℕ):Finset (E→₀ℕ):=
  (univ.image (fun w:E→Fin (k+1)=>Finsupp.equivFunOnFinite.symm (fun i=>(w i).val))).filter (fun n=>n.sum (fun _ t=>t)≤k)

private theorem inside (k:ℕ)(p:Normal.poly E)(deg:p.totalDegree≤k):p.support⊆stock E k:=by
  intro m hp
  have tot:m.sum (fun _ n=>n)≤k:=(MvPolynomial.le_totalDegree hp).trans deg
  have each (i:E):m i≤k:=by
    by_cases h:i∈m.support
    · exact (Finset.single_le_sum (fun j _=>Nat.zero_le (m j)) h).trans tot
    · simp [Finsupp.notMem_support_iff.mp h]
  unfold stock
  refine mem_filter.mpr ⟨mem_image.mpr ⟨fun i=>⟨m i,Nat.lt_succ_of_le (each i)⟩,mem_univ _,?_⟩,tot⟩
  ext i;rfl

private theorem account (k:ℕ)(p:Normal.poly E)(deg:p.totalDegree≤k): (∑d∈stock E k,‖MvPolynomial.coeff d p‖)=Rise.coin p:=by
  rw [Rise.metal]
  exact (Finset.sum_subset (inside k p deg) (fun d _ hd=>by simp [MvPolynomial.notMem_support_iff.mp hd])).symm

private theorem sum_ledger (k:ℕ)(p:Normal.poly E)(deg:p.totalDegree≤k): (∑d∈stock E k,MvPolynomial.monomial d (MvPolynomial.coeff d p))=p:=by
  calc _=∑ d∈p.support,MvPolynomial.monomial d (MvPolynomial.coeff d p):=
          (Finset.sum_subset (inside k p deg) (fun d _ hd=>by simp [MvPolynomial.notMem_support_iff.mp hd])).symm
       _=p:=MvPolynomial.support_sum_monomial_coeff p

def filed (k:ℕ)(A:ℕ→Normal.poly E):Normal.poly E:=
  ∑d∈stock E k,MvPolynomial.monomial d (∑' i,MvPolynomial.coeff d (A i))

theorem received (k:ℕ)(A:ℕ→Normal.poly E){C:ℝ}(deg:∀i,(A i).totalDegree≤k)(budget:SumBudget (fun i=>Rise.coin (A i)) C):
    (filed k A).totalDegree≤k ∧ Rise.coin (filed k A)≤C ∧
    ∀(x:E→ℂ),MvPolynomial.aeval x (filed k A)=∑' i,MvPolynomial.aeval x (A i):=by
  have fee (i:ℕ)(d:E→₀ℕ):‖MvPolynomial.coeff d (A i)‖≤Rise.coin (A i):=by
    by_cases hd:d∈(A i).support
    · rw [Rise.metal];exact Finset.single_le_sum (fun m _=>norm_nonneg (MvPolynomial.coeff m (A i))) hd
    · rw [MvPolynomial.notMem_support_iff.mp hd,norm_zero];exact budget.1 i
  have summ (d:E→₀ℕ):Summable (fun i=>MvPolynomial.coeff d (A i)):=Summable.of_norm_bounded budget.2.1 fun i=>fee i d
  have ns (d:E→₀ℕ):Summable (fun i=>‖MvPolynomial.coeff d (A i)‖):=Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=>fee i d) budget.2.1
  constructor
  · unfold filed;apply MvPolynomial.totalDegree_finsetSum_le;intro d hd
    exact (MvPolynomial.totalDegree_monomial_le ..).trans (mem_filter.mp hd).2
  constructor
  · calc Rise.coin (filed k A)≤∑ d∈stock E k,‖∑'i,MvPolynomial.coeff d (A i)‖:=by
           apply (Rise.collect 0 zero_le_one _ _).trans_eq
           simp only [Rise.tavern,one_pow,one_mul]
         _≤∑d∈stock E k,∑' i,‖MvPolynomial.coeff d (A i)‖:=sum_le_sum fun d _=>norm_tsum_le_tsum_norm (ns d)
         _=∑'i,∑ d∈stock E k,‖MvPolynomial.coeff d (A i)‖:=(Summable.tsum_finsetSum fun d _=>ns d).symm
         _=∑'i,Rise.coin (A i):=tsum_congr fun i=>account k (A i) (deg i)
         _≤C:=budget.2.2
  intro x
  let tag (d:E→₀ℕ):=MvPolynomial.aeval x (MvPolynomial.monomial d (1:ℂ))
  have value (d:E→₀ℕ)(z:ℂ):MvPolynomial.aeval x (MvPolynomial.monomial d z)=z*tag d:=by
    rw [←mul_one z,← MvPolynomial.C_mul_monomial,map_mul,MvPolynomial.aeval_C,mul_one];rfl
  calc MvPolynomial.aeval x (filed k A)=∑d∈stock E k,(∑' i,MvPolynomial.coeff d (A i))*tag d:=by simp only [filed,map_sum,value]
       _=∑d∈stock E k,∑' i,MvPolynomial.coeff d (A i)*tag d:=by simp only [tsum_mul_right]
       _=∑' i,∑d∈stock E k,MvPolynomial.coeff d (A i)*tag d:=(Summable.tsum_finsetSum fun d _=>(summ d).mul_right _).symm
       _=∑' i,MvPolynomial.aeval x (A i):=by
         apply tsum_congr;intro i;simpa only [map_sum,value] using congrArg (MvPolynomial.aeval x) (sum_ledger k (A i) (deg i))

end YM.Integration.WilsonCoherentMayerRootSeries
