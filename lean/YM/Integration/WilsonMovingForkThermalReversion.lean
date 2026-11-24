import YM.Integration.WilsonMovingForkCommonRawClocks

/-! Finite thermal reversion for the complete Laurent-cleared Wilson row. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingForkThermalReversion
open RegulatorIR RegulatorIR.Binding RegulatorIR.Profiles RegulatorIR.Clocks
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank PowerSeries
open WilsonIndependentPublicReportComplex (row)
open WilsonIndependentPublicReportBias
open WilsonMovingForkCommonRawClocks (heard bill)
open scoped Classical BigOperators PowerSeries

theorem diagonal (K : Feeds) (pole q : ℕ) : row K pole q q = 1 := by
  rw [WilsonIndependentPublicReportComplex.row_at K pole q q le_rfl,Nat.sub_self,coeff_zero_eq_constantCoeff]
  simp [map_mul, map_pow, back_cc (origin K)]

def recover (K : Feeds) (pole : ℕ) (observed : ℕ → ℂ) (q : ℕ) : ℂ :=
  observed q - ∑ i : Fin q, recover K pole observed i.val * (row K pole q i.val : ℂ)
termination_by q
decreasing_by exact i.isLt

theorem recover_heard (K : Feeds) (pole : ℕ) (bare : ℕ → ℂ) (q : ℕ) :
    recover K pole (fun j => heard K pole j bare) q = bare q := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    rw [recover]
    have smaller : (∑ i : Fin q, recover K pole (fun j => heard K pole j bare) i.val * (row K pole q i.val : ℂ)) =
        ∑ i : Fin q, bare i.val * (row K pole q i.val : ℂ) :=
      Finset.sum_congr rfl fun i _ => congrArg (fun x : ℂ => x*(row K pole q i.val : ℂ)) (ih i i.isLt)
    rw [smaller,Fin.sum_univ_eq_sum_range (fun i => bare i * (row K pole q i : ℂ))]
    unfold WilsonMovingForkCommonRawClocks.heard
    rw [WilsonIndependentPublicReportComplex.coefficients,Finset.sum_range_succ]
    simp only [coeff_mk,diagonal,Complex.ofReal_one,mul_one]
    ring

def inClock (newClock oldClock : Feeds) (newPole oldPole q : ℕ) (observed : ℕ → ℂ) : ℂ :=
  heard newClock newPole q (recover oldClock oldPole observed)

theorem transfer (first second : Feeds) (a b q : ℕ) (f : ℕ → ℂ) :
    inClock first second a b q (fun l => heard second b l f) = heard first a q f := by
  unfold inClock
  apply congrArg (heard first a q)
  funext i
  exact recover_heard second b f i

theorem charged (first second : Feeds) (a b q : ℕ) (f g : ℕ → ℂ) (income : ℕ → ℝ)
    (paid : ∀ j ≤ q, ‖f j-g j‖ ≤ income j) :
    ‖heard first a q f-inClock first second a b q (fun j => heard second b j g)‖ ≤ bill first a q income := by
  rw [transfer]
  exact WilsonMovingForkCommonRawClocks.on_film first a q f g income paid

end YM.Integration.WilsonMovingForkThermalReversion
