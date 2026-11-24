import YM.Integration.WilsonOriginalMicroscopicEntranceSlotCapital
import YM.Integration.WilsonOriginalAlternativeTrialPaidCourse

/-! A common before-cutoff budget at the birth scale for the actual fitted public basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceBirthCapital
open Finset Lattice Wilson RG Labels Source Marker PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open OPE.Therm
open WilsonOriginalMicroscopicEntranceGridBalance (coord)
open WilsonOriginalMicroscopicEntranceGridRow (factor)
open WilsonOriginalMicroscopicEntranceFlatWithdrawal (Returned)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)
local notation "H" i:max => R.family.path.levels.clock.hatBeta i
local notation "mesh" f:max => R.family.S.a f

theorem original {φ:Test 3}{simple:G.Simple}{tol:ℝ}{c q ℓ ear t stage cap:ℕ}{d b:Fin 3→ℕ}
    (grades:∀a,d a≤cap){Y:∀a:Fin 3,ℕ×ℕ→R.family.label (d a)}{f n N p:ℕ}{live:f+n≤N}
    {D:∀a:Fin 3,R.family.label (d a)≃ₗ[ℂ]R.family.label (d a)}{cash V:Fin 3→ℝ}
    (cp:∀a,0≤cash a)(vp:∀a,0≤V a){ε:ℝ}(small:ε≤1)
    (housing:(mesh f)/(mesh (f+n))≤(H f)^t*(H f)^ε)
    (posted:Returned R φ simple tol c q ℓ ear d b Y (p:=p) live D (fun a=>cash a*V a)
      (fun a=>cash a*((H f)^stage)⁻¹*(mesh f)^(d a)*V a)):
    let B:=∑j:Fin 3,cash j*V j
    ∀a,(R.family.labels.level (d a)).coeffSize ((factor R d (f+n) a) •
      coord R d b Y D N p a)≤B*(H (f+n))^((t+1)*(cap+1)):=by
  intro B a
  have own:=WilsonOriginalMicroscopicEntranceSlotCapital.original R cp vp small housing posted a
  have hf:1≤H f:=(R.family.path.levels.fits.delayed _).le
  have mono:H f≤H (f+n):=WilsonStartup.Timing.hat_mono _ (Gauge.slopeConstant_pos simple).le (Nat.le_add_right f n)
  have power:(H f)^((t+1)*(d a+1))≤(H (f+n))^((t+1)*(cap+1)):=by
    apply (pow_le_pow_left₀ (zero_le_one.trans hf) mono _).trans
    exact pow_le_pow_right₀ (hf.trans mono) (Nat.mul_le_mul_left _ (Nat.add_le_add_right (grades a) 1))
  have cost:cash a*V a≤B:=Finset.single_le_sum (fun j _=>mul_nonneg (cp j) (vp j)) (Finset.mem_univ a)
  calc _ ≤ _:=own
       _ ≤ (H (f+n))^((t+1)*(cap+1))*B:=mul_le_mul power cost (mul_nonneg (cp a) (vp a)) (pow_nonneg (zero_le_one.trans (hf.trans mono)) _)
       _ = _:=mul_comm _ _

end YM.Integration.WilsonOriginalMicroscopicEntranceBirthCapital
end
