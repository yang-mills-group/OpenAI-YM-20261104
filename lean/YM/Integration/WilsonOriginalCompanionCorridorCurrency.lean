import YM.Integration.WilsonOriginalCompanionTwinCredit
import YM.Integration.WilsonOriginalCompanionHardCurrency

/-! The single true source's original compulsory allowance pays the full logarithmic corridor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionCorridorCurrency
open Function Filter Lattice Wilson RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Trace.Physical.GermGraph RG05Readout RG05Readout.Many
open Pert.Asymptotics
open WilsonOriginalCompanionTwinCredit
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)
local notation "H" => R.family.path.levels.clock.hatBeta
def constant:ℝ:=49*4*4^6*(6:ℝ)^6
theorem bounded (f j l:ℕ):
    fare R f j l≤constant*(H f)^(36*(f-(j+2))+(5+(4+6*l)*6)):=by
  have one:1≤H f:=(R.family.path.levels.fits.delayed f).le
  have pos:0≤H f:=zero_le_one.trans one
  unfold fare constant
  calc _≤(49*(H f))*(H f)^4*4*4^6*(6*(H f)^(4+6*l))^6*(H f)^(36*(f-(j+2))):=by
          gcongr
          linarith
       _=_:=by rw [mul_pow,pow_add,pow_add,pow_mul];ring

theorem reserve (simple:G.Simple)(c l q:ℕ):∀ᶠ f:ℕ in atTop,∀j:ℕ,
    (f-(j+2):ℕ)≤(c:ℝ)*Real.log (RG16.Lambda R.family.path.levels f)+2 → ∀N p:ℕ,f≤N →
    LocalComparison.forcedDivisor R.family f*fare R f j l≤constant*(regulatorRun R.family N p f)^q:=by
  filter_upwards [WilsonOriginalCompanionHardCurrency.original R simple c 36 (5+(4+6*l)*6) q]
    with f credit j span N p fn
  have kp:0≤LocalComparison.forcedDivisor R.family f:=Real.sqrt_nonneg _
  calc _≤LocalComparison.forcedDivisor R.family f*(constant*(H f)^(36*(f-(j+2))+(5+(4+6*l)*6))):=
            mul_le_mul_of_nonneg_left (bounded R f j l) kp
       _=constant*(LocalComparison.forcedDivisor R.family f*(H f)^(36*(f-(j+2))+(5+(4+6*l)*6))):=by ring
       _≤_:=mul_le_mul_of_nonneg_left (credit _ span N p fn) (by unfold constant;norm_num)

end YM.Integration.WilsonOriginalCompanionCorridorCurrency
end
