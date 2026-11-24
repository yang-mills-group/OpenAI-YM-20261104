import YM.Integration.WilsonTwoAgeConditional
import YM.Integration.ActualTrajectoryTransport
import YM.Integration.RunFormalChain
import YM.RGComparison.Core16.Trajectory

/-! The three path integrals read the complete signed old terminal observable
and the separately submitted intermediate observable on the chosen run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonTwoAgeMeasuredRun
open Lattice RG Tree Wilson PhysicalNext.Repeat.Legato RGComparison.Core16 RGComparison.Core16.Descent
open scoped Classical
variable {G : Gauge} (R : Run G) {N per : ℕ} (Z : Slices R.family.path.levels per)

theorem previous {i : ℕ} (hi : i ≤ N) (A : Config G (R.family.side N per) → ℝ) :
    actualTransport R.family (N:=N) A hi =
      (traversal Z hi).conditioned (line R.family.path per i N) A := by
  induction hi using Nat.decreasingInduction with
  | self =>
    rw [actualTransport_base R.family R.makes le_rfl A,traversal_self]
    funext U
    change A U = (bare _ U)⁻¹ * (bare _ U * A U)
    rw [←mul_assoc,inv_mul_cancel₀ (bare_pos ..).ne',one_mul]
  | of_succ i hi ih =>
    rw [actualTransport_step R.family R.makes le_rfl A hi,ih]
    funext V
    rw [actualAverage_push,conditioned,vacuum_eq Z R.makes.wilson hi.le,weighted_step Z A hi]
    have pay (U : Config G (R.family.side (i+1) per)) :=
      conditional_times Z R.makes.wilson hi A U
    simp_rw [pay]

variable {i : ℕ} (hi : i < N)
local notation "S" => R.family.path.levels.clock.op i per
local notation "D" => traversal Z hi
local notation "β" => line R.family.path per i N

theorem average (F : Config G (R.family.side (i+1) per) → ℝ) (V : Config G (R.family.side i per)) :
    WilsonTwoAgeConditional.average S (Z i) D β F V = actualAverage R.family (N:=N) F V := by
  rw [actualAverage_push,WilsonTwoAgeConditional.average,←traversal_push Z hi,
    vacuum_eq Z R.makes.wilson hi.le,next_line,vacuum_eq Z R.makes.wilson hi]
  rfl

theorem original (A : Config G (R.family.side N per) → ℝ)
    (B : Config G (R.family.side (i+1) per) → ℝ)
    (ha : Continuous A) (ga : GaugeInvariant A) (hb : Continuous B) (gb : GaugeInvariant B)
    (V : Config G (R.family.side i per)) :
    let old := actualTransport R.family (N:=N) A (show i+1≤N from hi)
    actualAverage R.family (N:=N) (fun U=> B U * old U) V -
        actualAverage R.family (N:=N) old V * actualAverage R.family (N:=N) B V =
      WilsonTwoAgeConditional.reading S (Z i) D β A B V -
        WilsonTwoAgeConditional.reading S (Z i) D β A 1 V *
          WilsonTwoAgeConditional.reading S (Z i) D β 1 B V := by
  intro old
  have ok : (Descent.push S (Z i) D).OK G :=
    ⟨(R.family.path.levels.blocks i per).branches, traversal_ok Z hi⟩
  have equality := WilsonTwoAgeConditional.connected S (Z i) D ok β A B ha ga hb gb V
  simp_rw [average R Z hi, next_line] at equality
  dsimp only [old]
  rw [previous R Z hi A]
  exact equality

end YM.Integration.WilsonTwoAgeMeasuredRun
end
