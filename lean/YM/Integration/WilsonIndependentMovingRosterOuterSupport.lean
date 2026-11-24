import YM.Integration.WilsonIndependentFittedExteriorProfile
import YM.Integration.WilsonIndependentMovingRosterAnnulus

/-! Keep the actual translated exterior support when the physical radius falls between reporting levels. -/
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterOuterSupport
open Filter Function Lattice RG WilsonCoeffUV WilsonCoeffUV.Layout WilsonCoeffUV.Mer WilsonCoeffUV.Embroider Metric Set
open WilsonIndependentFittedExteriorProfile (home paid)
open scoped Topology BigOperators ContDiff

theorem relative {D:ℕ}(φ:Rarity D)(ρ:ℝ)(positive:0<ρ)(c q:Point4):
    (home φ ρ positive c).ψ.val q=ρ⁻¹^4*φ.ψ.val (ρ⁻¹ • (-c+q)):=by
  change ρ⁻¹^4*φ.ψ.val (address ρ⁻¹ 0 zeroC (0:Cover) (-c+q))=_
  rw [towards0]

theorem membership {D:ℕ}(φ:Rarity D)(ρ:ℝ)(positive:0<ρ)(c:Point4):
    tsupport (home φ ρ positive c).ψ.val⊆
      (fun q=>ρ⁻¹ • (-c+q)) ⁻¹' tsupport φ.ψ.val:=by
  have originalClosed:IsClosed (tsupport φ.ψ.val):=isClosed_closure
  have closed:IsClosed ((fun q:Point4=>ρ⁻¹ • (-c+q)) ⁻¹' tsupport φ.ψ.val):=
    originalClosed.preimage (by fun_prop)
  apply closure_minimal _ closed
  intro q hq
  apply subset_closure
  change φ.ψ.val (ρ⁻¹ • (-c+q))≠0
  intro zero
  change (home φ ρ positive c).ψ.val q≠0 at hq
  exact hq (by rw [relative,zero,mul_zero])

theorem original {D:ℕ}(φ:Rarity D)(ρ:ℝ)(one:1 ≤ ρ)(b:Point4)(d A:ℝ)(positive:0≤d)
    (profile:Amplitude φ A)(apart:∀x∈tsupport φ.ψ.val,d≤‖x+b‖):
    let ψ:=home φ ρ (zero_lt_one.trans_le one) (ρ • b)
    Amplitude ψ A ∧ ∀q∈tsupport ψ.ψ.val,d≤‖q‖:=by
  intro ψ
  have pos:=zero_lt_one.trans_le one
  have inv:0≤ρ⁻¹:=inv_nonneg.mpr pos.le
  have small:ρ⁻¹≤1:=inv_le_one_of_one_le₀ one
  have wage:=paid φ ρ pos (ρ • b) A profile
  rw [max_eq_left small,one_pow,one_mul] at wage
  refine ⟨⟨profile.1,fun j hj v x=>(wage.2 j hj v x).trans
    (mul_le_of_le_one_left profile.1 (pow_le_one₀ inv small))⟩,?_⟩
  intro q hq
  let v:=ρ⁻¹ • (-(ρ • b)+q)
  have originalSupport:v∈tsupport φ.ψ.val:=membership φ ρ pos (ρ • b) hq
  have chart:ρ • (v+b)=q:=by
    dsimp only [v]
    rw [smul_add,smul_smul,mul_inv_cancel₀ pos.ne',one_smul]
    abel
  calc d≤ρ*d:=le_mul_of_one_le_left positive one
       _≤ρ*‖v+b‖:=mul_le_mul_of_nonneg_left (apart v originalSupport) pos.le
       _=‖ρ • (v+b)‖:=by rw [norm_smul,Real.norm_of_nonneg pos.le]
       _=‖q‖:=congrArg _ chart

end YM.Integration.WilsonIndependentMovingRosterOuterSupport
