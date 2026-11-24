import YM.Integration.WilsonOriginalMicroscopicEntranceRawSalary
import YM.Integration.WilsonOriginalMicroscopicEntranceWithdrawalSlots

/-! The filed public trial pays its exact cutoff-normalized labels before the period is selected. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceSlotCapital
open Lattice Wilson RG Labels Source Marker PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open OPE.Therm
open WilsonOriginalMicroscopicEntranceGridBalance (coord slotFare)
open WilsonOriginalMicroscopicEntranceGridRow (factor)
open WilsonOriginalMicroscopicEntranceFlatWithdrawal (Returned)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)
local notation "H" f:max => R.family.path.levels.clock.hatBeta f
local notation "mesh" f:max => R.family.S.a f

theorem original {φ:Test 3}{simple:G.Simple}{tol:ℝ}{c q ℓ ear t stage:ℕ}{d b:Fin 3→ℕ}
    {Y:∀a:Fin 3,ℕ×ℕ→R.family.label (d a)}{f n N p:ℕ}{live:f+n≤N}
    {D:∀a:Fin 3,R.family.label (d a)≃ₗ[ℂ]R.family.label (d a)}
    {cash V:Fin 3→ℝ}(cp:∀a,0≤cash a)(vp:∀a,0≤V a){ε:ℝ}(small:ε≤1)
    (housing:(mesh f)/(mesh (f+n))≤(H f)^t*(H f)^ε)
    (posted:Returned R φ simple tol c q ℓ ear d b Y (p:=p) live D (fun a=>cash a*V a)
      (fun a=>cash a*((H f)^stage)⁻¹*(mesh f)^(d a)*V a))(a:Fin 3):
    ((R.family.labels.level (d a)).coeffSize
      ((factor R d (f+n) a) • (coord R d b Y D N p a)))≤(H f)^((t+1)*(d a+1))*(cash a*V a):=by
  obtain ⟨_,_,earned,_⟩:=posted (0,0)
  have one:1≤H f:=(R.family.path.levels.fits.delayed f).le
  have power:(H f)^ε≤H f:=(Real.rpow_le_rpow_of_exponent_le one small).trans_eq (Real.rpow_one _)
  have room:(mesh f)/(mesh (f+n))≤(H f)^(t+1):=by
    rw [pow_succ]
    exact housing.trans (mul_le_mul_of_nonneg_left power (pow_nonneg (zero_le_one.trans one) t))
  apply WilsonOriginalMicroscopicEntranceRawSalary.original R d (Nat.le_add_right f n) room _ (fun a=>cash a*V a)
    (fun a=>mul_nonneg (cp a) (vp a)) _ a
  intro i
  exact (earned i).1.trans (WilsonOriginalMicroscopicEntranceFlatWithdrawal.fee R f stage d cash V cp vp i)

end YM.Integration.WilsonOriginalMicroscopicEntranceSlotCapital
end
