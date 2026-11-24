import YM.Integration.WilsonMovingForkSharpGramAxisBox

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpGramArray
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonSeparatedPrefixMovingJointCell (toll)

open WilsonSeparatedPrefixMovingCellFactor (constant)
open WilsonIndependentMatchedCoverProfile
variable {G:Gauge}{H:Hol G}{n e h k D b m N older:ℕ}{C W V:Credit}

open WilsonSeparatedPrefixMovingJetBall (UnitJet)
variable {D j:ℕ}
variable {E:ℕ}
theorem growth (x:ℝ)(hx:0 ≤ x)(d f:ℕ):
    (1+x^d)*(1+x^f) ≤ 4*(1+x^(d+f)):=by
  by_cases small:x ≤ 1
  · have a:=pow_le_one₀ hx small (n:=d)
    have c:=pow_le_one₀ hx small (n:=f)
    have bound:=mul_le_mul (by linarith : 1+x^d ≤ 2) (by linarith : 1+x^f ≤ 2)
      (by positivity : 0 ≤ 1+x^f) (by norm_num : 0 ≤ (2:ℝ))
    nlinarith [pow_nonneg hx (d+f)]
  · have a:=pow_le_pow_right₀ (le_of_not_ge small) (Nat.le_add_right d f)
    have c:=pow_le_pow_right₀ (le_of_not_ge small) (Nat.le_add_left f d)
    rw [pow_add] at a c ⊢
    nlinarith [mul_nonneg (pow_nonneg hx d) (pow_nonneg hx f)]
theorem finite {U V:Type*}(S:Finset U)(T:Finset V)(x z A:ℝ)(K f:U→V→ℝ)
    (atEach:∀s t,‖f s t‖ ≤ K s t*A):
    ‖∑s∈S,x*∑t∈T,z*f s t‖ ≤ (∑s∈S,‖x‖*∑t∈T,‖z‖*K s t)*A:=by
  have row (s):‖∑t∈T,z*f s t‖ ≤ (∑t∈T,‖z‖*K s t)*A:=by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _=>?_)
    rw [norm_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (atEach s t) (norm_nonneg z)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _=>?_)
  rw [norm_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (row s) (norm_nonneg x)
end YM.Integration.WilsonMovingForkSharpGramArray
