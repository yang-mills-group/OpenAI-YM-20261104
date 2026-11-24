import YM.Integration.WilsonSeparatedPrefixMovingJointWaves
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The actual real separated source functions, with an operator price before frequency selection. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointWaveBudget
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonCoeffUV.Layout
open WilsonIndependentFittedExteriorProfile (home)
open WilsonIndependentMatchedCoverProfile (word)
variable {G:Gauge}{D:ℕ}



open Set
open scoped ContDiff
open WilsonSeparatedPrefixMovingAddressInk (writer)


open scoped ContDiff SchwartzMap
open WilsonSeparatedPrefixMovingJointWaves (sheet wave compose smooth)
theorem original (φ:Rarity D)(hf:ContDiff ℝ ∞ φ.ψ.val)(N:ℕ):
    ∃A:ℝ,0≤A ∧ ∀(ℓ:Point4→L[ℝ]ℝ)(c:Bool)(n:ℕ),n≤N→∀x:Point4,
    ‖iteratedFDeriv ℝ n (sheet φ ℓ c).ψ.val x‖≤ A*(1+‖ℓ‖)^N:=by
  classical
  have compact:HasCompactSupport φ.ψ.val:=(isCompact_closedBall (0:Point4) φ.radius).of_isClosed_subset
    (isClosed_tsupport _) φ.support
  let F:𝓢(Point4,ℝ):=compact.toSchwartzMap hf
  let a:=fun i:ℕ=>SchwartzMap.seminorm ℝ 0 i F
  let C:=∑i∈Finset.range (N+1),a i
  have ap (i:ℕ):0≤a i:=apply_nonneg (SchwartzMap.seminorm ℝ 0 i) F
  have cp:0≤C:=Finset.sum_nonneg fun i _=>ap i
  have localB (i:ℕ)(hi:i≤N)(x:Point4):‖iteratedFDeriv ℝ i φ.ψ.val x‖≤C:=by
    have z:‖iteratedFDeriv ℝ i F x‖≤ a i:=by simpa [a] using F.le_seminorm ℝ 0 i x
    exact z.trans (Finset.single_le_sum (fun j _=>ap j) (Finset.mem_range_succ_iff.mpr hi))
  refine ⟨(2:ℝ)^N*C,by positivity,?_⟩
  intro ℓ c
  let W:=(1+‖ℓ‖)^N
  intro n hn x
  apply le_trans (norm_iteratedFDeriv_mul_le hf ((smooth c).comp ℓ.contDiff) x (WithTop.coe_le_coe.mpr le_top))
  calc
    _ ≤ ∑i∈Finset.range (n+1),(n.choose i:ℝ)*(C*W):=by
      apply Finset.sum_le_sum
      intro i hi
      have ge:‖iteratedFDeriv ℝ (n-i) (wave c ∘ ℓ) x‖≤W:=(compose _ ℓ _ _).trans
        ((pow_le_pow_left₀ (norm_nonneg _) (by linarith : ‖ℓ‖≤1+‖ℓ‖) _).trans
         (pow_le_pow_right₀ (by linarith [norm_nonneg ℓ]:1≤1+‖ℓ‖) (by omega)))
      rw [←mul_assoc]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (localB i (by simp at hi;omega) x) (by positivity))
        ge (norm_nonneg _) (by positivity)
    _ = (2:ℝ)^n * (C*W):=by
      rw [←Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose n
    _ ≤ (2:ℝ)^N*C*W:=by rw [mul_assoc];gcongr; norm_num
end YM.Integration.WilsonSeparatedPrefixMovingJointWaveBudget
