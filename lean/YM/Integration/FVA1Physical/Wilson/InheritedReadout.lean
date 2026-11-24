import YM.Integration.FVA1Physical.Wilson.BareSolenoid
import YM.FVA2.RankHistory

/-! All mixed physical stencils along an arbitrary finite retained history.
The incoming solenoid ticket contains the entire previously integrated vacuum.
Its clock has the explicit inverse-coupling offsets at each interior level.
The estimates in this file evaluate the retained field at the identity. -/

noncomputable section
namespace YM.Integration.FVA1Physical.Wilson

open Function Filter Lattice RG Wilson Tree Precision Marker
open FVA2.CityHistory FVA2.CityHistory.Delay
open FormalOPE.RG10.InversionTop FormalOPE.RG10.MultiGauge FormalOPE.RG10.MarkovChain.Warp
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.WilsonXLocal
open PertExtension.Chart PertExtension.Series.Tested Extra.Trajectories
open scoped Classical ContDiff BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {V : Type} [DecidableEq V]
    {N p h : ℕ} (R : Census V) (U : V → Stamp.Reservation C (C.side N p) h)

private theorem joint_chart (s : R.Mode) (b : Bool) :
    ContDiffAt ℝ ∞ ((look b ∘ fullProduct (MSMatch.SourceTop.field U) s.val) ∘
      expLinks G (Edge (Site (C.side N p)))) 0 := by
  have hm : ContDiffAt ℝ ∞ (matrixField ∘ expLinks G (Edge (Site (C.side N p)))) 0 := by
    apply contDiffAt_pi.mpr
    intro e
    exact (G.exp_jet.of_le le_top).contDiffAt.comp (f := fun z : Pins G (C.side N p) => z e)
      0 (contDiff_apply ℝ G.Color e).contDiffAt
  have hl (i : V) : ContDiffAt ℝ ∞ (MSMatch.SourceTop.field U i ∘ expLinks G (Edge (Site (C.side N p)))) 0 := by
    let v := PertExtension.SameColumns.reprice C N p (Pi.single (U i).leg 1)
    rw [MSMatch.SourceTop.as_field U i]
    have ht := (observable_smooth C N p (U i).height v (U i).anchor).contDiffAt.comp
      (f := matrixField ∘ expLinks G (Edge (Site (C.side N p)))) 0 hm
    simpa only [Function.comp_def, observable_field] using ht
  exact (look b).contDiff.contDiffAt.comp 0 (contDiffAt_prod fun i _ => hl i)

variable {c f : Side} (d : Descent (C.side N p) f) (Z : ChartRatio G)
    (H : d.Room G) (v : d.Tags) (a : ℕ → ℝ)

/-- Fixed-offset independent coefficients of the retained Wilson integration.
One physical product and the same strictly positive vacuum enter the two components. -/
def historyCoefficient (s : R.Mode) (k : ℕ) : ℂ :=
  let F := fullProduct (MSMatch.SourceTop.field U) s.val
  let n := weight R (MSMatch.SourceTop.grade U) s + k
  let component := fun b : Bool => PowerSeries.coeff n (Stack.read 0
    (skyread Z d v H (stones a) (exPay (look b ∘ F))))
  ⟨component false, component true⟩

/-- The independently integrated joint Gaussian coefficients have exactly the
inherited-vacuum Wilson representation, after shifting by all the chosen field degrees. -/
theorem conditionalTerms_history (hZ : LocalRatio Z) (s : R.Mode) :
    conditionalTerms Z (MSMatch.SourceTop.field U) R (MSMatch.SourceTop.grade U) d a s =
      historyCoefficient R U d Z H v a s := by
  funext k
  let F := fullProduct (MSMatch.SourceTop.field U) s.val
  let n := weight R (MSMatch.SourceTop.grade U) s + k
  have eqn (b : Bool) := congrArg (PowerSeries.coeff n) (accrued Z hZ d H v a (joint_chart R U s b))
  have hr : (Complex.reCLM : ℂ → ℝ) = Complex.re := rfl
  have hi : (Complex.imCLM : ℂ → ℝ) = Complex.im := rfl
  apply Complex.ext
  · simpa [conditionalTerms, WilsonXLocal.kernel, historyCoefficient, n, look, hr] using eqn false
  · simpa [conditionalTerms, WilsonXLocal.kernel, historyCoefficient, n, look, hi] using eqn true

/-- The last RG step acts on the retained insertion from every earlier step,
including its covariance, action, field-dependent denominator and the new link Haar. -/
theorem history_at_push (S : StepData c f) (F : Forest S.ratio)
    (t : S.Choices) (hS : Bid.Larger (G := G) S) (hZ : LocalRatio Z)
    (s : R.Mode) (b : Bool) (k : ℕ) :
    let O := look b ∘ fullProduct (MSMatch.SourceTop.field U) s.val
    let n := weight R (MSMatch.SourceTop.grade U) s + k
    let previous := skyread Z d v H (stones (Descent.upβ a)) (exPay O)
    look b (historyCoefficient R U (Descent.push S F d) Z ⟨hS,H⟩ (t,v) a s k) =
      PowerSeries.coeff n (Stack.read 0 (solenoid S F d v t Z (stones a) hS H
        (boost (gate G S F) previous))) := by
  dsimp only
  have readout (q : Bool) : look q (historyCoefficient R U (Descent.push S F d) Z ⟨hS,H⟩ (t,v) a s k) =
      PowerSeries.coeff (weight R (MSMatch.SourceTop.grade U) s + k) (Stack.read 0
        (skyread Z (Descent.push S F d) (t,v) ⟨hS,H⟩ (stones a)
          (exPay (look q ∘ fullProduct (MSMatch.SourceTop.field U) s.val)))) := by cases q <;> rfl
  rw [readout, atop S F d v t Z (stones a) hZ hS H, stone_parent]

end YM.Integration.FVA1Physical.Wilson

