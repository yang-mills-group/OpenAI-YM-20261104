import YM.WilsonCoeffUV.Step.Source
import YM.RegulatorIR.Diagram.Drained

/-! The actual normalized Gaussian has the same finite polynomial moments as the Spout Wick operation. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalGaussianMoment
open WilsonCoeffUV WilsonCoeffUV.Blue RegulatorIR RegulatorIR.Diagram
open PertExtension PertExtension.GaussianScore MeasureTheory MvPolynomial
open scoped Classical BigOperators
variable {I E:Type} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (A:Law E)(d:I→Module.Dual ℝ E)(μ:Measure E)
    [μ.HasTemperateGrowth] [μ.IsAddRightInvariant] [NeZero μ]

private def weight (u:I→₀ℕ):ℕ:=∑ i,u i

theorem original (b:I→ℝ)(p:MvPolynomial I ℝ):
    Gaussian.averaged A d μ b p=emphasis b (glaze (Gaussian.bond A d) p) :=by
  classical
  let G:Matrix I I ℝ:=Gaussian.bond A d
  have symm:G.transpose=G:=by ext i j;exact Gaussian.bond_cross A d j i
  have mon (u:I→₀ℕ)(a:ℝ):Gaussian.averaged A d μ b (monomial u a)=emphasis b (glaze G (monomial u a)):=by
    generalize hr:weight u=k
    induction k using Nat.strong_induction_on generalizing u a with
    | h k prev =>
      by_cases zero:u=0
      · subst u
        change Gaussian.averaged A d μ b (C a)=emphasis b (glaze G (C a))
        rw [Gaussian.average_const,glaze_constant,language,MvPolynomial.eval_C]
      have existsPos:∃ i,u i≠0:=by
        by_contra! neg
        exact zero (Finsupp.ext neg)
      obtain ⟨i,hi⟩:=existsPos
      let v:=u-Finsupp.single i 1
      have small:Finsupp.single i 1≤u:=by
        intro j
        by_cases h:i=j
        · subst j;simp;omega
        · simp [h]
      have split:v+Finsupp.single i 1=u:=tsub_add_cancel_of_le small
      have count:weight v+1=k:=by
        rw [←hr,←split]
        simp [weight,Finset.sum_add_distrib,Finsupp.single_apply]
      have prior:weight v<k:=by omega
      have formula:monomial u a=monomial v a * X i:=by
        rw [X,monomial_mul,split,mul_one]
      rw [formula,Gaussian.recipe,wick_poly G symm,map_add,map_mul,show emphasis b (X i)=b i by rw [language];simp,
        prev _ prior v a rfl,map_sum]
      rw [mul_comm (b i)]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      have rank:weight (v-Finsupp.single j 1)≤weight v:=by
        apply Finset.sum_le_sum;intro l _;exact Nat.sub_le _ _
      have term:=prev _ (rank.trans_lt prior) (v-Finsupp.single j 1) (a*v j) rfl
      rw [pderiv_monomial,term,map_smul]
      rfl
  induction p using MvPolynomial.induction_on' with
  | monomial u a=>exact mon u a
  | add p q hp hq=>rw [Gaussian.average_add,hp,hq,map_add,map_add]

end YM.Integration.WilsonIndependentConditionalGaussianMoment
