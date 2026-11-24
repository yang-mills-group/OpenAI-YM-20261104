import YM.Integration.WilsonIndependentConditionedEarlierRoom

/-! Evaluate the finite clock-and-profile polynomial at genuine subpower room parameters. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedEarlierThermal
open Filter Real Function Lattice Wilson RG RG.Supply Precision PhysicalNext.Repeat.Legato
open Next.Rank WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol Extra.Histories
open WilsonIndependentConditionedBankFittedFees (age)
open WilsonIndependentConditionedActualCredit (badge gramAge homes)
open WilsonInvariantActionPosition (berth)
open scoped Topology Classical
variable {G:Gauge}(R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta


open WilsonIndependentConditionedEarlierRoom (Room)
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
local notation "J" => Fin 2

theorem original (simple:G.Simple)(P:Credit){ε:ℝ}(ep:0<ε):
    ∃η:ℝ,0<η ∧ ∀ᶠ f:ℕ in atTop,∀(t z:ℝ)(B:J→ℝ),
      |t⁻¹|≤(thermal R f)^(-η) → |z|≤(thermal R f)^(-η) → (∀s,|B s|≤(thermal R f)^(-η)) →
      P.buy (Room.amount (badge R f) t z B) ≤ (thermal R f)^(-ε):=by
  let η:=ε/(2*((P.d:ℝ)+1))
  have eta:0<η:=div_pos ep (by positivity)
  have top:η*((P.d:ℝ)+1)=ε/2:=by
    dsimp only [η]
    field_simp
  let A₀:Credit:=⟨0,max 1 (P.x*6^P.d),le_max_left ..⟩
  let C₀:Credit:=⟨1,1,le_rfl⟩
  have warm:=(tendsto_log_atTop.comp (Station.hat_rate R.family.path.levels simple)).eventually_ge_atTop 1
  refine ⟨η,eta,?_⟩
  filter_upwards [warm,WilsonIndependentConditionedActualCredit.subpower R simple A₀ (half_pos ep),
    WilsonIndependentConditionedActualCredit.subpower R simple C₀ eta] with f heat fixed var
  intro t z B ti room film
  let g:=thermal R f
  have bp:=R.family.path.levels.fits.delayed f
  have positive:0<g:=inv_pos.mpr (sqrt_pos.mpr (zero_lt_one.trans bp))
  have small:g≤1:=inv_le_one_of_one_le₀ (one_le_sqrt.mpr bp.le)
  have bill:P.x*6^P.d ≤ g^(-(ε/2)):=by
    have t: max 1 (P.x*6^P.d) ≤ g^(-(ε/2)):=by simpa only [A₀,Credit.buy,pow_zero,mul_one] using fixed
    exact (le_max_right ..).trans t
  have cap:badge R f ≤ g^(-η):=by simpa only [C₀,Credit.buy,pow_one,one_mul] using var
  have one:1≤badge R f:=heat
  have amount:Room.amount (badge R f) t z B≤6*g^(-η):=by
    dsimp only [Room.amount]
    linarith only [cap,one,ti,room,film 0,film 1]
  have ap:0 ≤ Room.amount (badge R f) t z B:=by
    unfold Room.amount
    linarith only [one,abs_nonneg t⁻¹,abs_nonneg z,abs_nonneg (B 0),abs_nonneg (B 1)]
  have tarif:(g^(-η))^P.d ≤ g^(-(ε/2)):=by
    rw [←rpow_natCast,←rpow_mul positive.le]
    apply rpow_le_rpow_of_exponent_ge positive small
    linarith only [top,eta]
  calc
    P.buy (Room.amount (badge R f) t z B) ≤ P.x*(6*g^(-η))^P.d :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ap amount _) (zero_le_one.trans P.good)
    _ = (P.x*6^P.d)*(g^(-η))^P.d:=by rw [mul_pow];ring
    _ ≤ g^(-(ε/2))*g^(-(ε/2)):=mul_le_mul bill tarif (pow_nonneg (rpow_nonneg positive.le _) _)
      (rpow_nonneg positive.le _)
    _ = g^(-ε):=by rw [←rpow_add positive];congr 1;ring

end YM.Integration.WilsonIndependentConditionedEarlierThermal
