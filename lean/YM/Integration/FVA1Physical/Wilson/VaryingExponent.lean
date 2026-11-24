import YM.Integration.FVA1Physical.Wilson.ClockPhaseJets
import YM.Integration.FVA1Physical.Wilson.VaryingAccount

/-! Remove the pure Gaussian from the actual variable-clock action.
Every remaining Taylor coefficient on the chart is the independently
computed FVA2 interaction input, including every inherited reset. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter RG Lattice RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice
open FVA2 FVA2.CityHistory FVA2.CityHistory.Legacy FVA2.RayScatter PowerSeries
open scoped Classical Topology ContDiff
variable {G : Gauge} {n c : Side} (d : Descent n c) (t : d.Tags) (u : Pins G c) (h : d.OK G)
    (z : ℕ → ℝ → ℝ) (w : ℕ → PowerSeries ℝ) (hot : ∀ i ≤ d.depth, ContDiffAt ℝ ω (z i) 0)
    (hw : ∀ i ≤ d.depth, Aspiration (z i) (term (w i)))

include h hot hw in
theorem phase_series (x : Coordinates G d) :
    mk (fun i => jet (clockPhase d t u z) i (1,x)) = X^2 + read (x,u) (moneyX d t w) := by
  have small : Aspiration (fun g : ℝ => g^2) (term ((X : PowerSeries ℝ)^2)) := by
    rw [show term ((X : PowerSeries ℝ)^2) = fun i => if i=2 then 1 else 0 from funext fun i => coeff_X_pow i 2]
    simpa [smul_eq_mul] using Aspiration.single (1:ℝ) 2
  have A := small.add (actual_account_coefficients d t h z w hw (x,u))
  have same (g : ℝ) : clockPhase d t u z (g • ((1:ℝ),x)) =
      g^2 + consume d t (fun i => z i g) (g • (x,u)) := by
    rw [clockPhase_exact,map_smul,recovery]
    simp
  have B := directions ((clockPhase_hot d t u h hot).of_le le_top) ((1:ℝ),x)
  simp_rw [same] at B
  have H := B.unique A
  apply PowerSeries.ext
  intro i
  rw [coeff_mk,congrFun H i,map_add]
  rfl

include h hot hw in
theorem varied_layers (heads : SoundZ w) (x : Coordinates G d) (k : ℕ) :
    layers (clockPhase d t u z) k (1,x) = coeff k (read (x,u) (entryPay d t w)) := by
  by_cases zero : k=0
  · subst k
    rw [Stationary.layers_zero,reading_term,coeff_zero_eq_constantCoeff_apply,startPay h t w]
    rfl
  have phase := congrArg (coeff (k+2)) (phase_series d t u h z w hot hw x)
  simp only [coeff_mk,map_add,coeff_X_pow,if_neg (show k+2 ≠ 2 by omega),zero_add] at phase
  have payment := congrArg (fun M => coeff (k+2) (read (x,u) M)) (issueZ (G:=G) h t w heads)
  simp only [map_mul,map_pow,show read (x,u) (X : Ticket (SpaceF G d)) = X from PowerSeries.map_X _,
    coeff_X_pow_mul,map_sub,map_neg] at payment
  have vac : coeff k (read (x,u) (C (coeff 2 (rise (consume d t (G:=G) 1))))) = 0 := by
    unfold Stack.read
    rw [map_C,coeff_C,if_neg zero]
  rw [vac,sub_zero] at payment
  simp only [Radial.layers,if_neg zero,add_zero,phase,payment]

theorem read_exponent_congr {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (x : E) (y : F) (A : Ticket E) (B : Ticket F)
    (same : read x A = read y B) : read x (exponential A) = read y (exponential B) := by
  apply PowerSeries.ext
  intro k
  rw [reading_term,reading_term,exponential,exponential,coeff_mk,coeff_mk,← reading_term,← reading_term]
  simp only [map_sum,map_mul,map_pow,rollThrough,same]

include h hot hw in
theorem varied_interaction (heads : SoundZ w) (x : Coordinates G d) :
    read (1,x) (exponential (advancing (clockPhase d t u z))) =
      read (x,u) (exponential (entryPay d t w)) := by
  apply read_exponent_congr
  apply PowerSeries.ext
  intro k
  rw [levels,varied_layers d t u h z w hot hw heads]

end YM.Integration.FVA1Physical.Wilson
