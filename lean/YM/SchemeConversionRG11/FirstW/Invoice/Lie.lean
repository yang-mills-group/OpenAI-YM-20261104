import YM.SchemeConversionRG11.FirstW.Invoice.Strike
/-! Chosen-leg price expansions. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace YM.RG11.FirstW.Deck
open Function Filter MeasureTheory ProbabilityTheory Set Lattice Pert Warp Topology Maxwell
open scoped BigOperators Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsGaussian μ] {I : Type*} [Fintype I] [DecidableEq I] (t : I → Query E)
variable (p : Cache I) (Y Z D : Query E)
local notation "v" => MvPolynomial.pderiv (R:=ℂ)
def dotF (p : Cache I) := ∫ x, spend t p x ∂μ
def payOne (p : Cache I) (Y : Query E) := ∫ x, Y x * spend t p x ∂μ
def payTwo (p : Cache I) (Y Z : Query E) := ∫ x, Y x * (Z x * spend t p x) ∂μ
def payTree (p : Cache I) (Y Z D : Query E) := ∫ x, Y x * (Z x * (D x * spend t p x)) ∂μ
lemma one_bill (h : ∀ i,Laugh μ (t i)) (hy : Laugh μ Y) : payOne μ t p Y = ∑ i, coins μ Y (t i)*dotF μ t (v i p) := by
  have H:= takeoff μ t Y h hy p (fun _=>Y) ∅ (fun _=> hy)
  simpa only [payOne,priceD,dotF,refundC,extra,Finset.prod_empty,one_mul,Finset.sum_empty,zero_add] using H
lemma two_bill (h : ∀ i,Laugh μ (t i)) (hy : Laugh μ Y) (hz : Laugh μ Z) : payTwo μ t p Y Z = coins μ Y Z * dotF μ t p + ∑ i, coins μ Y (t i)*payOne μ t (v i p) Z := by
  have H:= takeoff μ t Y h hy p (fun _=>Z) {0} (fun _=>hz)
  simpa only [payTwo,priceD,dotF,payOne,refundC,extra,Finset.prod_singleton,Finset.sum_singleton,Finset.erase_singleton,Finset.prod_empty,one_mul] using H
lemma tree_bill (h : ∀ i,Laugh μ (t i)) (hy : Laugh μ Y) (hz : Laugh μ Z) (hd : Laugh μ D) : payTree μ t p Y Z D = coins μ Y Z * payOne μ t p D + coins μ Y D * payOne μ t p Z + ∑ i, coins μ Y (t i)*payTwo μ t (v i p) Z D := by
  let K (i : ℕ) := if i=0 then Z else D
  have ht (i : ℕ):Laugh μ (K i) := by
    unfold K; split <;> assumption
  have H := takeoff μ t Y h hy p K {0,1} ht
  simp [payOne,payTwo, payTree]; simpa [refundC,priceD,extra,K,mul_assoc,show ({0,1}:Finset ℕ).erase 1={0} from by decide] using H
lemma erase_two (h : ∀ i,Laugh μ (t i)) (hy : Laugh μ Y) (hz : Laugh μ Z) : payTwo μ t p Y Z=coins μ Y Z*dotF μ t p + ∑ i,∑ j, coins μ Y (t i)*(coins μ Z (t j)*dotF μ t (v j (v i p))) := by
  rw [two_bill μ t p Y Z h hy hz]; simp_rw [one_bill μ t (v _ p) Z h hz,Finset.mul_sum]
lemma erase_tree (h : ∀ i,Laugh μ (t i)) (hy : Laugh μ Y) (hz : Laugh μ Z) (hd : Laugh μ D) : payTree μ t p Y Z D = coins μ Y Z * payOne μ t p D + coins μ Y D * payOne μ t p Z + coins μ Z D * payOne μ t p Y + ∑ i,∑ j,∑ k, coins μ Y (t i)*coins μ Z (t j)*coins μ D (t k)*dotF μ t (v k (v j (v i p))) := by
  rw [tree_bill μ t p Y Z D h hy hz hd,one_bill μ t p Y h hy]; simp_rw [erase_two μ t (v _ p) Z D h hz hd,mul_add,Finset.mul_sum,Finset.sum_add_distrib]; simp_rw [show ∀ i:I, coins μ Y (t i)*(coins μ Z D*dotF μ t (v i p))= _ from fun i=>mul_left_comm _ _ _]; simp_rw [mul_assoc, ←add_assoc] -- rw under binder
end YM.RG11.FirstW.Deck
