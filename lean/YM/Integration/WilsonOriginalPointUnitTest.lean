import YM.Integration.WilsonOriginalPointModes

/-! A genuine unit test takes value one at the native point on every orbit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPointModes
open Finset LocalComparison ComparisonDensity.Address
open scoped Classical Topology ContDiff
variable {V : Type}

theorem constant_bill (U : Orbit) : U.Bill (fun _=> (1:ℂ)) 1 := by
  refine ⟨zero_le_one,contDiff_const,?_⟩
  intro k _ z _
  cases k with
  | zero =>
    rw [norm_iteratedFDeriv_zero,norm_one,mul_one]
    exact one_le_pow₀ (by linarith [norm_nonneg z])
  | succ k =>
    simp only [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k),Pi.zero_apply,norm_zero,mul_one]
    exact (U.sky z).le

def unit (D : V→Orbit) : IndependentTests D := fun i=>⟨fun _=>1,constant_bill (D i)⟩

theorem unit_read (D : V→Orbit) (i : V) : (testInclusion D (unit D) i).val 0=1 := rfl

theorem root_bound (D : V→Orbit) (x : IndependentTests D) (i : V) : ‖(x i).val 0‖≤1 := by
  have bound := (x i).property.limits 0 (Nat.zero_le _) 0 (D i).dawn
  simpa only [norm_iteratedFDeriv_zero,Orbit.flat,mul_one] using bound

end YM.Integration.WilsonOriginalPointModes
