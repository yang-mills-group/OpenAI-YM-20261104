import YM.Integration.WilsonOriginalCensusPageOrbits

/-! The one original volume normalization spends the winding fee once across
the common-root orbit, including for the field-independent marked coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusDeckMean
open Finset Lattice RG Wilson
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalConnectedPeriodPage
open scoped Classical BigOperators
variable {n X:Side}(h:n.val∣X.val)

def mean (f:Deck h→ℂ):ℂ:=(Pages n X:ℂ)⁻¹*∑d,f d

theorem volume:Fintype.card (Deck h)=Pages n X:=by
  let p:Fin (Pages n X):=(page h 0).symm ⟨0,(posted ..).mpr (map_zero _)⟩
  simpa only [Fintype.card_fin] using Fintype.card_congr (WilsonOriginalPinnedDeckOrbit.around h 0 p)

theorem constant (z:ℂ):mean h (fun _=>z)=z:=by
  have pos:0<Pages n X:=pow_pos (Nat.div_pos (Nat.le_of_dvd X.pos h) n.pos) _
  simp only [mean,sum_const,card_univ,volume,nsmul_eq_mul]
  field_simp [show (Pages n X:ℂ)≠0 by exact_mod_cast pos.ne']

theorem paid (f g:Deck h→ℂ)(E:ℝ)(single:∀d,‖f d-g d‖ ≤ E):‖mean h f-mean h g‖ ≤ E:=by
  have pos:0<Pages n X:=pow_pos (Nat.div_pos (Nat.le_of_dvd X.pos h) n.pos) _
  have cash:0 ≤ (Pages n X:ℝ)⁻¹:=by positivity
  unfold mean
  rw [←mul_sub,←Finset.sum_sub_distrib,norm_mul,norm_inv,Complex.norm_natCast]
  calc
    _ ≤ (Pages n X:ℝ)⁻¹*∑d,‖f d-g d‖:=mul_le_mul_of_nonneg_left (norm_sum_le _ _) cash
    _ ≤ (Pages n X:ℝ)⁻¹*∑_d:Deck h,E:=mul_le_mul_of_nonneg_left (sum_le_sum (fun d _=>single d)) cash
    _ = E:=by
      simp only [sum_const,card_univ,volume,nsmul_eq_mul]
      field_simp [show (Pages n X:ℝ)≠0 by exact_mod_cast pos.ne']

end YM.Integration.WilsonOriginalCensusDeckMean
end
