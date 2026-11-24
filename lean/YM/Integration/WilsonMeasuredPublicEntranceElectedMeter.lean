import YM.Integration.WilsonMeasuredPublicEntranceFixedBill
import YM.Integration.WilsonAddressedFiniteGuardEars

/-! A single before-cutoff order pays the two regular readings, the older mixed trial, and the original unmasking. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceElectedMeter
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics WilsonOriginalOccupiedStencil
open Multi Comparison.RG02.Cumulants
open Filter Finset Lattice Wilson RG Marker QuadraticLocal WilsonThermometerMixedCollarSubpower
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V](d:V → ℕ)
local notation "H" i:max => R.family.path.levels.clock.hatBeta i
local notation "J" => Stock.census V
local notation "ord" => WilsonMeasuredPublicEntranceFixedBill.order

theorem original (simple:G.Simple)(B:ℝ)(target:ℕ):
    ∀ᶠ f:ℕ in atTop,∀N per K (_:f ≤ N)(_ : f ≤ K)(s:(J).Mode),
    let p:=ord target
    let g:=regulatorRun R.family N per f
    2*((H f)^p)⁻¹+
      (g^p*(2*((shards (J) s).card:ℝ)+1)+WilsonAddressedFiniteGuardEars.fare R (K:=K) d B 1 p s.val)
      ≤ ((H f)^target)⁻¹:=by
  let r:=target+1
  let raw (s:(J).Mode):ℝ:=WilsonAddressedFiniteGuardCapital.price R d B s.val*
    ((WilsonAddressedFiniteGuardCapital.count R d s.val:ℝ)*(4*Real.exp 102))
  let mass(s:(J).Mode):ℝ:=2+2^r*(2*((shards (J) s).card:ℝ)+1)+abs (raw s)
  have pos(s):0 ≤ mass s:=by dsimp [mass];positivity
  filter_upwards [(RG01.Physical.hats simple R.family.path.levels).eventually_ge_atTop (∑s,mass s)] with f ready
  intro N per K fn fk s p g
  have one:1 ≤ H f:=(R.family.path.levels.fits.delayed f).le
  have hp:0<H f:=zero_lt_one.trans_le one
  have later:H f ≤ H K:=WilsonStartup.Timing.hat_mono _ (Gauge.slopeConstant_pos simple).le fk
  have hk:0<H K:=hp.trans_le later
  let D:=((H f)^r)⁻¹
  have dp:0 ≤ D:=inv_nonneg.mpr (pow_nonneg hp.le _)
  have times:r ≤ p:=by dsimp [p,WilsonMeasuredPublicEntranceFixedBill.order,r];omega
  have small:((H f)^p)⁻¹ ≤ D:=inv_anti₀ (pow_pos hp _) (pow_le_pow_right₀ one times)
  have guard:((H K)^p)⁻¹ ≤ D:=(inv_anti₀ (pow_pos hp _) (pow_le_pow_left₀ hp.le later p)).trans small
  have billed:=WilsonCapturedPrimaryPointMatrixClock.band R (per:=per) fn
  have earn:g^p ≤ 2^r*D:=by
    apply (le_mul_inv_iff₀ (pow_pos hp r)).mpr
    change g^(2*r)*(H f)^r ≤ 2^r
    rw [pow_mul,←mul_pow,mul_comm (g^2)]
    exact pow_le_pow_left₀ (mul_nonneg hp.le (sq_nonneg g)) billed _
  have halo:WilsonAddressedFiniteGuardEars.fare R (K:=K) d B 1 p s.val ≤ abs (raw s)*D:=by
    calc _=raw s*((H K)^p)⁻¹:=by
           change WilsonAddressedFiniteGuardCapital.price R d B s.val*
             ((WilsonAddressedFiniteGuardCapital.count R d s.val:ℝ)*(4*Real.exp 102)*(1/(H K)^p))=_
           unfold raw
           rw [one_div];ring
         _ ≤ abs (raw s)*((H K)^p)⁻¹:=mul_le_mul_of_nonneg_right (le_abs_self _) (inv_nonneg.mpr (pow_nonneg hk.le _))
         _ ≤ abs (raw s)*D:=mul_le_mul_of_nonneg_left guard (abs_nonneg _)
  have part:=Finset.single_le_sum (fun s (_:s∈univ)=>pos s) (Finset.mem_univ s)
  calc _ ≤ 2*D+(2^r*D*(2*((shards (J) s).card:ℝ)+1)+abs (raw s)*D):=
      add_le_add (mul_le_mul_of_nonneg_left small (by norm_num))
        (add_le_add (mul_le_mul_of_nonneg_right earn (by positivity)) halo)
       _=mass s*D:=by dsimp [mass];ring
       _ ≤ (H f)*D:=mul_le_mul_of_nonneg_right (part.trans ready) dp
       _=((H f)^target)⁻¹:=by dsimp [D,r];rw [pow_succ,mul_inv_rev];field_simp

end YM.Integration.WilsonMeasuredPublicEntranceElectedMeter
end
