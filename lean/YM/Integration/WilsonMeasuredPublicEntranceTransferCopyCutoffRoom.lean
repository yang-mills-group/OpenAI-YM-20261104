import YM.Integration.WilsonOriginalPublicTrialPhaseRate
import YM.Integration.WilsonRootedTwoDateHardHeadroom

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCopyCutoffRoom
open Finset Real Lattice RG Wilson Extra.Multi PhysicalNext.Repeat.Legato
open WilsonOriginalPublicTrialPhaseRate (wage volume room)
open private radius from YM.Integration.WilsonRootedTwoDateHardHeadroom
variable {G:Gauge}(R:Run G){K N p:ℕ}
local notation "C" => R.family
local notation "P" => (C).path.rep N p K
local notation "H" => (C).path.levels.clock.hatBeta K

def tariff (load:ℕ):ℝ:=2*(5:ℝ)^4*(1+load)*(1+exp 1*82^4)/log 2

theorem original (live:K≤N)(load:ℕ)(χ:ℝ):
    (wage (P).p.B load χ)⁻¹≤tariff load*H^16*(1+|χ|):=by
  let B:=(P).p.B
  have real:(P).p=(C).path.levels.budget K:=(R.makes.wilson.represents N p K live).vac
  have rad:(B:ℝ)≤2*H^2:=by simpa [B,real] using radius R K
  have one:1≤H:=((C).path.levels.fits.delayed K).le
  have h0:0≤H:=zero_le_one.trans one
  have h2:1≤H^2:=one_le_pow₀ one
  have h8:1≤H^8:=one_le_pow₀ one
  have logp:0<log 2:=Real.log_pos (by norm_num)
  have vol:volume B≤5^4*H^8:=by
    unfold volume
    push_cast
    calc _≤(5*H^2)^4:=pow_le_pow_left₀ (by positivity) (by linarith only [rad,h2]) 4
         _=_:=by ring
  have site:1+|siteFactor B|≤(1+exp 1*82^4)*H^8:=by
    unfold siteFactor
    rw [abs_of_nonneg (by positivity)]
    have b:=pow_le_pow_left₀ (by positivity : 0≤2*(16*(B:ℝ)+9))
      (show 2*(16*(B:ℝ)+9)≤82*H^2 by linarith only [rad,h2]) 4
    have e:=mul_le_mul_of_nonneg_left b (exp_pos 1).le
    calc _≤1+exp 1*(82*H^2)^4:=by linarith
         _≤H^8+exp 1*(82*H^2)^4:=by linarith
         _=_:=by ring
  have train:=mul_le_mul vol site (by positivity) (by positivity)
  change (wage B load χ)⁻¹≤_
  unfold wage room tariff
  field_simp [ne_of_gt logp,show 0<1+|χ| by positivity,show volume B≠0 by unfold volume;positivity,
    show 0<1+(load:ℝ) by positivity,show 0<1+|siteFactor B| by positivity]
  nlinarith only [train]
end YM.Integration.WilsonMeasuredPublicEntranceTransferCopyCutoffRoom
end
