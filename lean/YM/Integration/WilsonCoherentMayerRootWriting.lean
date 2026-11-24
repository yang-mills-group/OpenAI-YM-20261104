import YM.Integration.WilsonCoherentMayerRootSeries
import YM.WilsonCoeffUV.Reclosure.Revenue

/-! A signed average of the complete, countable original polynomial deposit. -/

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section
namespace YM.Integration.WilsonCoherentMayerRootWriting
open Finset Work.F08 RG Laurent Lattice Wilson Bloch
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoherentMayerRootSeries
open scoped BigOperators Classical
variable {E:Type*}

theorem income {c:ℕ→ℝ}{D b:ℝ}(cash:SumBudget c D)(hb:0≤b)(A:ℕ→Normal.poly E)
    (tails:∀i,Rise.coin (A i)≤c i*b):SumBudget (fun i=>Rise.coin (A i)) (D*b):=by
  have full:=cash.2.1.mul_right b
  have live:=full.of_nonneg_of_le (fun i=>Rise.sign 0 (A i) zero_le_one) tails
  exact ⟨fun i=>Rise.sign 0 (A i) zero_le_one,live,(live.tsum_le_tsum tails full).trans (by rw [tsum_mul_right];exact mul_le_mul_of_nonneg_right cash.2.2 hb)⟩

variable [Fintype E]

def blended (k:ℕ)(A:Signed→ℕ→Normal.poly E):Normal.poly E:=
  MvPolynomial.C ((Fintype.card Signed:ℂ)⁻¹) * ∑ s:Signed,filed k (A s)

theorem original (k:ℕ)(A:Signed→ℕ→Normal.poly E){D:ℝ}(deg:∀s i,(A s i).totalDegree≤k)
    (b:∀s,SumBudget (fun i=>Rise.coin (A s i)) D):
    (blended k A).totalDegree≤k ∧ Rise.coin (blended k A)≤D ∧
    ∀z:E→ℂ,MvPolynomial.aeval z (blended k A)=((Fintype.card Signed:ℂ)⁻¹)*∑ s:Signed,∑' i,MvPolynomial.aeval z (A s i):=by
  have h s:=received k (A s) (deg s) (b s)
  refine ⟨?_,?_,?_⟩
  · unfold blended
    apply (MvPolynomial.totalDegree_mul ..).trans
    rw [MvPolynomial.totalDegree_C,zero_add]
    apply MvPolynomial.totalDegree_finsetSum_le;exact fun s _=>(h s).1
  · unfold blended
    apply (Rise.funds 0 zero_le_one _ _).trans
    rw [Rise.pay_C,norm_inv,Complex.norm_natCast]
    have hn:0<(Fintype.card Signed:ℝ):=by exact_mod_cast Fintype.card_pos
    calc
      _ ≤ (Fintype.card Signed:ℝ)⁻¹ * ∑ s:Signed,Rise.coin (filed k (A s)):=mul_le_mul_of_nonneg_left (Rise.collect 0 zero_le_one _ _) (inv_nonneg.mpr hn.le)
      _ ≤ (Fintype.card Signed:ℝ)⁻¹ * ∑ _:Signed,D:=mul_le_mul_of_nonneg_left (sum_le_sum fun s _=>(h s).2.1) (inv_nonneg.mpr hn.le)
      _ = D:=by simp [nsmul_eq_mul,hn.ne']
  · intro z
    unfold blended
    simp only [map_mul,map_sum,MvPolynomial.aeval_C]
    simp_rw [fun s=>(h s).2.2 z]
    rfl

end YM.Integration.WilsonCoherentMayerRootWriting
