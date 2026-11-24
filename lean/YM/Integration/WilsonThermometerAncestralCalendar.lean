import YM.Integration.WilsonReceivedCloseChainFunding
import YM.Integration.WilsonWindowReportingPace
import YM.Integration.WilsonDyadicReportingPrice

/-! Convert the physical count of soft close dates into the calendar receipt of
the original qlocal course before either regulator is chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerAncestralCalendar
open Filter Finset Lattice Wilson RG RG16 QuadraticLocal.Advent
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "z" i:max => Real.log (2+Real.log (R.alloy.B.a.clock.hatBeta i))

include simple in
theorem counted (slow:∀ j,((R.family.S.block j).val:ℝ) ≤ Real.log (Lambda R.family.path.levels j))
    (degree:ℕ) {C:ℝ} (cap:0 ≤ C) {i t:ℕ} (it:i ≤ t)
    (days:((t-i:ℕ):ℝ) ≤ C*(z i)^degree) : PaceR.Close R (degree+1) C i t :=by
  have mono {j n:ℕ} (jn:j ≤ n) : z j ≤ z n := by
    have clock:=Real.log_le_log (PaceR.positive R j) (PaceR.clock_mono R simple jn)
    exact Real.log_le_log (by linarith only [PaceR.positive_log R j]) (by linarith only [clock])
  have pos (j:ℕ) : 0 ≤ z j := Real.log_nonneg (by linarith only [PaceR.positive_log R j])
  have step (j:ℕ) (jt:j ≤ t) : Real.log ((R.family.S.block j).val:ℝ) ≤ z t :=
    (Real.log_le_self (by exact_mod_cast (R.family.S.block j).property.le)).trans ((slow j).trans (mono jt))
  have interval : ∀n,i ≤ n → n ≤ t → R.family.S.scale n - R.family.S.scale i ≤ ((n-i:ℕ):ℝ)*(z t) :=by
    intro n h
    induction h with
    | refl =>simp
    | @step j ij ih =>
      intro jt
      have last:=step j (by omega)
      have before:=ih (by omega)
      have crossing : j+1-i=(j-i)+1 := Nat.succ_sub ij
      rw [R.family.S.scale_succ,crossing,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
      linarith only [last,before]
  unfold PaceR.Close
  calc R.family.S.scale t - R.family.S.scale i ≤ ((t-i:ℕ):ℝ)*(z t) := interval t it le_rfl
       _ ≤ (C*(z i)^degree)*(z t) := mul_le_mul_of_nonneg_right days (pos t)
       _ ≤ (C*(z t)^degree)*(z t) := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pos i) (mono it) _) cap) (pos t)
       _ = _ := by rw [pow_succ,mul_assoc]

include simple in
theorem two (slow:∀ j,((R.family.S.block j).val:ℝ) ≤ Real.log (Lambda R.family.path.levels j))
    (i:ℕ):PaceR.Close R 1 2 i (i+2) :=by
  exact counted R simple slow 0 (by norm_num) (by omega) (by simp)

include simple in
theorem weak : ∀ᶠ i:ℕ in atTop,∀ N per j:ℕ,i ≤ j → j ≤ N → 0<regulatorRun R.family N per j ∧
    regulatorRun R.family N per j ≤ 1 :=by
  filter_upwards [WilsonReceivedCloseChainFunding.upper R simple 0 0,
    WilsonDyadicReportingPrice.reserve (C:=R.family) simple R.makes 3 0 1 (by norm_num) zero_lt_one]
    with i rows price
  intro N per j ij jN
  have bound:=rows i le_rfl (by simp [PaceR.Close]) N per (ij.trans jN) j ij jN
  exact ⟨bound.1,bound.2.trans (by simpa only [Real.rpow_zero,mul_one] using price per N (ij.trans jN))⟩

end YM.Integration.WilsonThermometerAncestralCalendar
