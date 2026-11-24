import YM.Integration.WilsonIndependentConditionedBankBerth

/-! The selected true optical depth pays the low and high fitted tariffs at different orders. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankClosing
open Filter Lattice RG Wilson PhysicalNext.Repeat.Legato
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
open WilsonInvariantActionPosition (berth)
open scoped Topology
variable {G:Gauge}(R:Run G)
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "a" => R.family.S.a

theorem beta (f X:ℕ):(β f)^X=(thermal R f)^(-((2*X:ℕ):ℝ)):=by
  have bp:0<β f:=zero_lt_one.trans (R.family.path.levels.fits.delayed f)
  have tp:0 ≤ thermal R f:=(inv_pos.mpr (Real.sqrt_pos.mpr bp)).le
  rw [Real.rpow_neg tp,Real.rpow_natCast]
  change (β f)^X=((((Real.sqrt (β f))⁻¹)^(2*X))⁻¹)
  rw [pow_mul,inv_pow,Real.sq_sqrt bp.le,inv_pow,inv_inv]

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (T q H E₀ E₁:ℕ)(P ε ξ B:ℝ)(gain:0 ≤ ξ)(nb:0 ≤ B)
    (low:P+ε+((2*E₀:ℕ):ℝ) ≤ ((2*T:ℕ):ℝ)*ξ)
    (high:P+ε+((2*E₁:ℕ):ℝ) ≤ ((q+1:ℕ):ℝ)-((2*(T+1):ℕ):ℝ)*H):
    ∀ᶠ f:ℕ in atTop,let g:=thermal R f; let K:=berth R T f; let δ:=a K/a f
      ∀X Y u:ℝ,X ≤ g^(-ε) → Y ≤ g^(-ε) → |u| ≤ B*g →
        (X*(β f)^E₀)*δ^ξ + (Y*(β f)^E₁)*(|u|^(q+1)*(δ^H)⁻¹) ≤ (1+B^(q+1))*g^P:=by
  filter_upwards [WilsonIndependentConditionedBankBerth.acquired R simple slow T] with f bought
  intro g K δ X Y u eX eY orbit
  have hot:0<g:=bought.2.1
  have small:g ≤ 1:=bought.2.2.1
  have dp:0<δ:=div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)
  have fine:δ ≤ g^((2*T:ℕ):ℝ):=by simpa only [Real.rpow_natCast] using bought.2.2.2.2
  have lower:g^(2*(T+1)) ≤ δ:=bought.2.2.2.1
  have eδ:δ^ξ ≤ g^(((2*T:ℕ):ℝ)*ξ):=by
    rw [Real.rpow_mul hot.le]
    exact Real.rpow_le_rpow dp.le fine gain
  have tax (n:ℕ):0 ≤ (β f)^n:=pow_nonneg (zero_lt_one.trans (R.family.path.levels.fits.delayed f)).le _
  have smallL: X*(β f)^E₀*δ^ξ ≤ g^P:=calc
    _ ≤ g^(-ε)*(β f)^E₀*g^(((2*T:ℕ):ℝ)*ξ):=
      mul_le_mul (mul_le_mul_of_nonneg_right eX (tax _)) eδ (Real.rpow_nonneg dp.le _)
        (mul_nonneg (Real.rpow_nonneg hot.le _) (tax _))
    _ = g^(-ε-((2*E₀:ℕ):ℝ)+((2*T:ℕ):ℝ)*ξ):=by
      rw [beta]
      change g^(-ε)*g^(-((2*E₀:ℕ):ℝ))*_=_
      rw [←Real.rpow_add hot,←Real.rpow_add hot]
      congr 1
    _ ≤ _:=Real.rpow_le_rpow_of_exponent_ge hot small (by linarith only [low])
  have co:(δ^H)⁻¹ ≤ (g^((2*(T+1))*H))⁻¹:=by
    rw [pow_mul]
    exact (inv_le_inv₀ (pow_pos dp _) (pow_pos (pow_pos hot _) _)).2
      (pow_le_pow_left₀ (pow_nonneg hot.le _) lower _)
  have temp:|u|^(q+1) ≤ B^(q+1)*g^(q+1):=by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) orbit _
  have scaled:(Y*(β f)^E₁)*(|u|^(q+1)*(δ^H)⁻¹) ≤ B^(q+1)*g^P:=calc
    _ ≤ (g^(-ε)*(β f)^E₁)*((B^(q+1)*g^(q+1))*(g^((2*(T+1))*H))⁻¹):=
      mul_le_mul (mul_le_mul_of_nonneg_right eY (tax _))
        (mul_le_mul temp co (by positivity) (by positivity)) (by positivity)
        (mul_nonneg (Real.rpow_nonneg hot.le _) (tax _))
    _ = B^(q+1)*(g^(-ε)*(β f)^E₁*g^(q+1)*(g^((2*(T+1))*H))⁻¹):=by ring
    _ = B^(q+1)*g^(-ε-((2*E₁:ℕ):ℝ)+((q+1:ℕ):ℝ)-((2*(T+1):ℕ):ℝ)*H):=by
      rw [beta,←Real.rpow_natCast g (q+1),←Real.rpow_natCast g ((2*(T+1))*H),←Real.rpow_neg hot.le]
      change B^(q+1)*(g^(-ε)*g^(-((2*E₁:ℕ):ℝ))*_ * _)=_
      rw [←Real.rpow_add hot,←Real.rpow_add hot,←Real.rpow_add hot]
      congr 2
      push_cast
      ring
    _ ≤ _:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hot small (by linarith only [high]))
      (pow_nonneg nb _)
  simpa only [add_mul,one_mul] using add_le_add smallL scaled

theorem before (P ε ζ:ℝ)(pos:0<ζ)(H E₀ E₁:ℕ):
    ∃T:ℕ,∀t≥T,∃Q:ℕ,∀q≥Q,
      P+ε+((2*E₀:ℕ):ℝ) ≤ ((2*t:ℕ):ℝ)*(3*ζ/4) ∧
      P+ε+((2*E₁:ℕ):ℝ) ≤ ((q+1:ℕ):ℝ)-((2*(t+1):ℕ):ℝ)*H:=by
  obtain ⟨T,low⟩:=WilsonAddressedTrialKineticAperture.reserve (wanted:=P+ε)
    (pole:=((2*E₀:ℕ):ℝ)) pos
  refine ⟨T,fun t later=>?_⟩
  obtain ⟨Q,hQ⟩:=exists_nat_ge (P+ε+((2*E₁:ℕ):ℝ)+((2*(t+1):ℕ):ℝ)*H)
  refine ⟨Q,fun q late=>⟨low t later,?_⟩⟩
  have step:(Q:ℝ) ≤ ((q+1:ℕ):ℝ):=by exact_mod_cast (Nat.le_succ_of_le late)
  linarith only [hQ,step]

end YM.Integration.WilsonIndependentConditionedBankClosing
