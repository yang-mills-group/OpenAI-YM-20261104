import YM.Integration.WilsonPositionHomogeneousFrame
import YM.GradedFar.Funds
/-!
# The physical clock hypothesis used at the formal estimate, and its source

Use the original hypothesis `Trace.Pilot.Coupling G` *on the actual reading*. This is the
**previous hypothesis** t ~ g on the prescribed thermometer (not on a regulator beta,
and NOT a conclusion of Main.Match). See `poseFit_coupling`: in bbcb it's supplied via (F.3)
with t'_ℓ ~ g in that lemma. We give the derivation from that version of the earlier inputs too,
using the price on the genuine **tested log** in the true continuum and its actual normalized read.
No need for later hypotheses G.1, G.6, G.9 to buy the bridge here.

This takes previous hypotheses of the prescribed construction. `PoseFit` isn't being proved
from scratch. In particular exporting a theorem on formal prediction with this evaluation
hypothesis does **not** assert we've proved the kinetic law, much less the actual-to-formal
comparison. See README for dependencies and physical suppliers required.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open Function Filter Set PowerSeries
open Wilson RG Source Extraction Table Spec PhysicalNext.Repeat.Legato RG17 FullVolume
open Climb Trace.Pilot PhysMS
open XSpace XSpace.Normalize FVA2 FVA2.Register
open scoped Topology BigOperators Classical

variable {G : Gauge} (hG : G.Simple)

include hG
local notation "g" => strength G
variable {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (N : WilsonPrescription G)
local notation "t" => WilsonPositionHomogeneousFrame.reading F J N
local notation "W" => WilsonPositionPrescribedFrame.positioned F J N.store
local notation "tested" => WilsonPositionThermometerReading.tested F W N.criterion
local notation "cT" => Rose.cT N.criterion.cut G N.criterion.image

theorem measured_budget (ht : Coupling G t) :
    ∀ᶠ r in trail, 0 < g r ∧ |t r| ≤ 1 ∧ |t r| ≤ 2 * g r := by
  -- supplier for calendar g, sign, and price order. Use only this bridge before detector inversion.
  filter_upwards [strength_positive hG, ht.positive, (ratio_clock hG ht).eventually_lt_const (show (1:ℝ) < 2 by norm_num),
    (Coupling.conforms hG ht).eventually_lt_const zero_lt_one] with r hr hQ hr' hr''
  rw [abs_of_pos hQ]; exact ⟨ hr, le_of_lt hr'', le_of_lt ((div_lt_iff₀ hr).mp hr') ⟩

/-- Use the preceding estimates t'_ℓ/g → 1 and the price on the continuum test (F.3).
Thus a source of the measured clock hypothesis used in M.2. State the (F.3) input
at any order `M-1 ≥ 2`; this proof uses the estimate with that much slack (also not its sign
or its other field consequences). -/
theorem poseFit_coupling (t' : ℝ → ℝ) (m : ℕ) (ht' : Tendsto (fun r => t' r / g r) trail (𝓝 1))
    {C : ℝ} (hT : ∀ᶠ r in trail, ‖tested r - ((cT * t' r : ℝ) : ℂ)‖ ≤ C * (g r)^(m+2)) :
    Coupling G t := by
  let a : ℝ := cT
  have hn : a ≠ 0 := N.criterion.fresh.ne
  have he : Tendsto (fun r => t r / g r) trail (𝓝 1) := by
    have hten := Coupling.conforms hG (strength_coupling hG)
    have hkey : Tendsto (fun r => C / |a| * (g r)^(m+1)) trail (𝓝 0) := by
      simpa only [ne_eq, Nat.add_one_ne_zero, not_false_eq_true, zero_pow, mul_zero]
        using (hten.pow (m+1)).const_mul (C/|a|)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (show Tendsto (fun r => t' r/g r - C/|a| * (g r)^(m+1)) trail (𝓝 1) from by
        simpa only [sub_zero] using ht'.sub hkey) (show Tendsto (fun r => t' r/g r +
        C/|a| * (g r)^(m+1)) trail (𝓝 1) from by simpa only [add_zero] using ht'.add hkey)
    all_goals
      filter_upwards [strength_positive hG,hT] with r hr hb
      have ha : |t r/g r - t' r/g r| ≤ C/|a| * (g r)^(m+1) := by
        have htest : (tested r).re = a * t r :=
          (WilsonPositionThermometerReading.calibrated_denominator F W N.criterion r).symm
        replace hb := (Complex.abs_re_le_norm _).trans hb
        rw [Complex.sub_re, Complex.ofReal_re, htest] at hb
        change |a*t r-a*t' r| ≤ C*_ at hb
        rw [← mul_sub, abs_mul] at hb
        rw [← sub_div, abs_div, abs_of_pos hr, div_le_iff₀ hr]
        have h := (le_div_iff₀ (abs_pos.mpr hn)).mpr (show |t r-t' r| * |a| ≤ C * (g r)^(m+2) from by rwa [mul_comm])
        convert h using 1; ring
      replace ha := abs_le.mp ha; linarith
  have hf : ∀ᶠ r in trail, 0 < t r := by
    filter_upwards [strength_positive hG, he.eventually_const_lt zero_lt_one] with r hr hp
    exact (div_pos_iff.mp hp).elim (fun h => h.1) (fun h => False.elim (hr.not_gt h.2))
  refine ⟨hf, ?_⟩
  have hv := (strength_coupling hG).running.mul (he.pow 2)
  rw [one_pow, mul_one] at hv
  refine hv.congr' ((strength_positive hG).mono (fun r hr => ?_)); field_simp

end YM.Integration.GradedFar
