import YM.Integration.WilsonConditionalTaylorThermalNextProduct

/-! The three surviving terms two orders above a pair of graded factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalSecondProduct
open Function PowerSeries RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Series Radial Tested WilsonConditionalTaylorThermalDivision
open scoped Classical BigOperators ContDiff
theorem convolution {A B : ℕ → ℝ} {a b : ℕ} (ha : ∀i<a,A i=0) (hb : ∀i<b,B i=0) :
    (∑z∈Finset.antidiagonal (a+b+2),A z.1*B z.2)=
      A a*B (b+2)+A (a+1)*B (b+1)+A (a+2)*B b := by
  let t := Finset.antidiagonal (a+b+2)
  have h₀ : (a,b+2)∈t := Finset.mem_antidiagonal.mpr (by omega)
  have h₁ : (a+1,b+1)∈t := Finset.mem_antidiagonal.mpr (by omega)
  have h₂ : (a+2,b)∈t := Finset.mem_antidiagonal.mpr (by omega)
  have each (z) (hz : z∈t) : A z.1*B z.2 =
      ((if z=(a,b+2) then A a*B (b+2) else 0)+(if z=(a+1,b+1) then A (a+1)*B (b+1) else 0))+
        (if z=(a+2,b) then A (a+2)*B b else 0) := by
    obtain rfl|h1 := eq_or_ne z (a,b+2)
    · simp
    obtain rfl|h2 := eq_or_ne z (a+1,b+1)
    · simp
    obtain rfl|h3 := eq_or_ne z (a+2,b)
    · simp
    simp only [h1,h2,h3,if_false,add_zero]
    have sum := Finset.mem_antidiagonal.mp hz
    by_cases low : z.1<a
    · rw [ha _ low,zero_mul]
    rw [hb z.2 (by
      by_contra! high
      have shape : z.1=a ∨ z.1=a+1 ∨ z.1=a+2 := by omega
      rcases shape with h|h|h
      · exact h1 (Prod.ext h (show z.2=b+2 by omega))
      · exact h2 (Prod.ext h (show z.2=b+1 by omega))
      · exact h3 (Prod.ext h (show z.2=b by omega))),mul_zero]
  change (∑z∈t,A z.1*B z.2)=_
  rw [Finset.sum_congr rfl each,Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp [h₀,h₁,h₂]

theorem series {A B : PowerSeries ℝ} {a b : ℕ} (ha : zeroBefore A a) (hb : zeroBefore B b) :
    coeff (a+b+2) (A*B)=coeff a A*coeff (b+2) B+coeff (a+1) A*coeff (b+1) B+coeff (a+2) A*coeff b B := by
  rw [coeff_mul];exact convolution ha hb

theorem jets {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A F : E→ℝ} (sa : ContDiffAt ℝ ∞ A 0) (sf : ContDiffAt ℝ ∞ F 0)
    {a b : ℕ} (ha : RadialOrder a A) (hb : RadialOrder b F) (x : E) :
    jet (A*F) (a+b+2) x=jet A a x*jet F (b+2) x+jet A (a+1) x*jet F (b+1) x+jet A (a+2) x*jet F b x := by
  have eq := congrFun ((directions (f:=A*F) (sa.mul sf) x).unique ((directions sa x).prod (directions sf x))) (a+b+2)
  dsimp only [conv,term] at eq
  rw [PowerSeries.coeff_mul] at eq
  simp only [PowerSeries.coeff_mk] at eq
  exact eq.trans (convolution (fun _ hi=>congrFun (jets_vanish sa ha hi) x)
    (fun _ hi=>congrFun (jets_vanish sf hb hi) x))

end YM.Integration.WilsonConditionalTaylorThermalSecondProduct
