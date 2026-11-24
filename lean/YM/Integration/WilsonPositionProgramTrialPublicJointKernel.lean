import YM.Integration.WilsonPositionProgramTrialPublicJointCredit

/-! Joint continuity and the uniform multiplier bound for the actual normalized filed modes. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointKernel
open RG WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer Precision Lattice MeasureTheory
open WilsonPositionProgramTrialPublicJointCredit (price)
open WilsonPositionProgramTrialPublicJointRoom (width big normalized)
open WilsonSeparatedPrefixMovingJointWaves (wave)
open WilsonSeparatedPrefixMovingJointSpectrum (physical)
open WilsonSeparatedPrefixMovingJointExpansion (angle)
open scoped Classical Topology BigOperators
variable {n:ℕ}
def leaf {D:Fin n→ℕ}(T:(i:Fin n)→Rarity (D i))(x:Points n):ℂ:=
  ((∏i,(T i).ψ.val (physical (x i)):ℝ):ℂ)
def oscillation (D:Fin n→ℕ)(c:Fin n→Bool)(ξ x:Points n):ℂ:=
  ∏i,(((width ξ^D i)⁻¹*wave (c i) (2*Real.pi*inner ℝ (ξ i) (x i)):ℝ):ℂ)
theorem value {D:Fin n→ℕ}(T:(i:Fin n)→Rarity (D i))(ξ x:Points n)(c:Fin n→Bool):
    leaf (normalized T ξ c) x=leaf T x*oscillation D c ξ x:=by
  have angle_at (i:Fin n):angle (ξ i) (physical (x i))=2*Real.pi*inner ℝ (ξ i) (x i):=by simp [WilsonSeparatedPrefixMovingJointExpansion.angle]
  unfold leaf oscillation
  push_cast
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  change (((width ξ^D i)⁻¹*((T i).ψ.val (physical (x i))*wave (c i) (angle (ξ i) (physical (x i)))):ℝ):ℂ)=_
  rw [angle_at]
  push_cast
  ring

theorem bounded (D:Fin n→ℕ)(c:Fin n→Bool)(ξ x:Points n):‖oscillation D c ξ x‖≤1:=by
  unfold oscillation
  rw [norm_prod]
  apply Finset.prod_le_one (fun _ _=>norm_nonneg _)
  intro i _
  have p:1≤width ξ ^D i:=one_le_pow₀ (big ξ)
  have iv:(width ξ^D i)⁻¹≤1:=inv_le_one_of_one_le₀ p
  have w:|wave (c i) (2*Real.pi*inner ℝ (ξ i) (x i))|≤1:=by
    cases hc:c i
    · exact abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
    · exact abs_le.mpr ⟨Real.neg_one_le_sin _,Real.sin_le_one _⟩
  rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans p))]
  exact (mul_le_mul_of_nonneg_right iv (abs_nonneg _)).trans (by simpa only [one_mul] using w)

theorem regular (D:Fin n→ℕ)(c:Fin n→Bool):
    Continuous (fun v:Points n×Points n=>oscillation D c v.1 v.2):=by
  classical
  have wc:Continuous (width:Points n→ℝ):=by unfold width;fun_prop
  have invw (i:Fin n):Continuous (fun v:Points n×Points n=>(width v.1^D i)⁻¹):=
    ((wc.comp continuous_fst).pow (D i)).inv₀ (fun v=>(pow_pos (zero_lt_one.trans_le (big v.1)) _).ne')
  have each (i:Fin n):Continuous (fun v:Points n×Points n=>
      (((width v.1^D i)⁻¹*wave (c i) (2*Real.pi*inner ℝ (v.1 i) (v.2 i)):ℝ):ℂ)):=by
    apply Complex.continuous_ofReal.comp
    apply (invw i).mul
    apply (WilsonSeparatedPrefixMovingJointWaves.smooth (c i)).continuous.comp
    have proj:Continuous (fun t:Points n=>t i):=(PiLp.proj (𝕜:=ℝ) 2 (fun _:Fin n=>E4) i).continuous
    exact continuous_const.mul ((proj.comp continuous_fst).inner (proj.comp continuous_snd))
  exact continuous_finsetProd _ (fun i _=>each i)

end YM.Integration.WilsonPositionProgramTrialPublicJointKernel
end
