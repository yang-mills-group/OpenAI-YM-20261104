import YM.QuadraticLocal.Earn.Blend
import YM.QuadraticLocal.Germ.Annual

/-! Engineering rescaling is implemented inside the formal input row.
Keeping the physical atom, test, support and salary fixed pays its inverse
coupling power without charging an inverse power to the test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.CP5
open Finset Lattice YM.Wilson RG Marker QuadraticLocal.Earn QuadraticLocal.Affinity
open scoped Classical BigOperators
variable {G:Gauge} {I α:Type} [DecidableEq I] {n:Side} {P:Passport n I} {J:Census I}

def fieldToll (h:ℕ) := max 1 (h-1)

def engineeringRow (X:Row P J G α) (h:ℕ) (grade:h≤X.lamp.r) : Row P J G α :=
  {X with lamp := ⟨X.lamp.r-h,X.lamp.r,fieldToll h,
    (Nat.zero_lt_one.trans_le (le_max_left ..)),by unfold fieldToll; omega⟩}

theorem engineering_payload (X:Row P J G α) (h:ℕ) (grade:h≤X.lamp.r) (flat:X.lamp.e=X.lamp.r)
    (g:ℝ) (t:α) (U:Config G n) :
    (engineeringRow X h grade).nominal g t U =
      (((g^h)⁻¹:ℝ):ℂ) * X.nominal g t U := by
  have lag : ((X.lamp.r-h:ℕ):ℤ) - (X.lamp.r:ℤ) = -(h:ℤ) := by omega
  change X.paint t * (((g^(((X.lamp.r-h:ℕ):ℤ)-(X.lamp.r:ℤ)) * X.atom.unmasked U X.center):ℝ):ℂ) =
    ((g^h)⁻¹:ℝ) * (X.paint t * (((g^((X.lamp.e:ℤ)-X.lamp.r)*X.atom.unmasked U X.center):ℝ):ℂ))
  rw [lag,flat,sub_self,zpow_zero,one_mul,zpow_neg,zpow_natCast,Complex.ofReal_mul]
  ring

end YM.Integration.FVA1Physical.Round2.CP5
