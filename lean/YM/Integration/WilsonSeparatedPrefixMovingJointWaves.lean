import YM.Integration.WilsonSeparatedPrefixMovingJointSpectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The actual real separated source functions, with an operator price before frequency selection. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointWaves
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
def wave:Bool→ℝ→ℝ|false=>Real.cos|true=>Real.sin
theorem smooth (c:Bool):ContDiff ℝ ∞ (wave c):=by cases c <;> simp only [wave] <;> fun_prop
theorem bounded (n:ℕ)(c:Bool)(x:ℝ):‖iteratedFDeriv ℝ n (wave c) x‖≤1:=by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  induction n generalizing c with
  | zero=>cases c <;> simp only [iteratedDeriv_zero,wave,Real.norm_eq_abs] <;>
      first | exact Real.abs_cos_le_one _ | exact Real.abs_sin_le_one _
  | succ n ih=>
    cases c
    · simpa only [wave,Real.iteratedDeriv_add_one_cos,Pi.neg_apply,norm_neg] using ih true
    · simpa only [wave,Real.iteratedDeriv_add_one_sin] using ih false
theorem compose (c:Bool)(ℓ:Point4→L[ℝ]ℝ)(n:ℕ)(x:Point4):
    ‖iteratedFDeriv ℝ n (wave c ∘ ℓ) x‖≤‖ℓ‖^n:=by
  rw [ℓ.iteratedFDeriv_comp_right (smooth c) x (WithTop.coe_le_coe.mpr le_top)]
  exact ((iteratedFDeriv ℝ n (wave c) (ℓ x)).norm_compContinuousLinearMap_le (fun _:Fin n=>ℓ)).trans
    (by simpa using mul_le_mul_of_nonneg_right (bounded n c (ℓ x)) (pow_nonneg (norm_nonneg ℓ) n))
def sheet (φ:Rarity D)(ℓ:Point4→L[ℝ]ℝ)(c:Bool):Rarity D where
  ψ:=⟨fun x=>φ.ψ.val x*wave c (ℓ x),(scribble φ.ψ le_rfl).mul (((smooth c).of_le (WithTop.coe_le_coe.mpr le_top)).comp ℓ.contDiff)⟩
  radius:=φ.radius
  markG:=φ.markG
  support:=by
    apply Subset.trans _ φ.support
    apply closure_mono
    intro p hp
    change φ.ψ.val p * wave c (ℓ p)≠0 at hp
    exact left_ne_zero_of_mul hp
theorem original (φ:Rarity D)(hf:ContDiff ℝ ∞ φ.ψ.val):
    ∃A:ℝ,0≤A ∧ ∀(ℓ:Point4→L[ℝ]ℝ)(c:Bool),Amplitude (sheet φ ℓ c) (A*(1+‖ℓ‖)^D):=by
  classical
  have compact:HasCompactSupport φ.ψ.val:=(isCompact_closedBall (0:Point4) φ.radius).of_isClosed_subset
    (isClosed_tsupport _) φ.support
  let F:𝓢(Point4,ℝ):=compact.toSchwartzMap hf
  let a:=fun i:ℕ=>SchwartzMap.seminorm ℝ 0 i F
  let C:=∑i∈Finset.range (D+1),a i
  have ap (i:ℕ):0≤a i:=apply_nonneg (SchwartzMap.seminorm ℝ 0 i) F
  have cp:0≤C:=Finset.sum_nonneg fun i _=>ap i
  have localB (i:ℕ)(hi:i≤D)(x:Point4):‖iteratedFDeriv ℝ i φ.ψ.val x‖≤C:=by
    have z:‖iteratedFDeriv ℝ i F x‖≤ a i:=by simpa [a] using F.le_seminorm ℝ 0 i x
    exact z.trans (Finset.single_le_sum (fun j _=>ap j) (Finset.mem_range_succ_iff.mpr hi))
  refine ⟨(2:ℝ)^D*C,by positivity,?_⟩
  intro ℓ c
  let W:=(1+‖ℓ‖)^D
  have wp:0≤W:=by dsimp [W];positivity
  refine ⟨by positivity,?_⟩
  intro n hn v x
  change ‖iteratedFDeriv ℝ n (fun x=>φ.ψ.val x * wave c (ℓ x)) x (Embroider.dot ∘ v)‖≤_
  apply le_trans (ContinuousMultilinearMap.le_opNorm _ _)
  simp only [Function.comp_apply,Embroider.dot,Pi.norm_single,norm_one,Finset.prod_const_one,mul_one]
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
    _ ≤ (2:ℝ)^D*C*W:=by rw [mul_assoc];gcongr; norm_num
end YM.Integration.WilsonSeparatedPrefixMovingJointWaves
