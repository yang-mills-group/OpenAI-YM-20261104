import YM.Integration.FVA1Physical.Round2.TestBank
import YM.Integration.FVA1Physical.Round2.VoiceProduct

/-! The remainder constant for a mixed product of actual C18 field
insertions is chosen before all bounded, independent physical voices.
The coefficient bank uses the independent FVA2 conditional Wilson step. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Filter Function Finset MeasureTheory Lattice RG YM.Wilson Tree Precision
open RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.WilsonXLocal
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open FVA2.CityHistory FormalOPE.RG10.MultiGauge Comparison.RG02
open LocalLTE.Sail Labels
open scoped Classical Topology ContDiff BigOperators
variable {I : Type} {G : Gauge} {N n : ℕ} {H : History G} (Y : Batch H N n I)
    (s : Finset I) {c : Side} (d : Descent (H.S.side N n) c) {Z : ChartRatio G}
    (hZ : LocalRatio Z) (h : d.Room G) (tag : d.Tags) (u : Pins G c) (a : ℕ → ℝ)
    (L : ℂ →L[ℝ] ℝ)

include hZ in
theorem physical_voice_price (r : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (v : ∀ i, ((frames G).level (Y.demand i)).Coeff),
      (∀ i, ((frames G).level (Y.demand i)).coeffSize (v i) ≤ 1) →
      let O := L ∘ fullProduct (retest Y v).wavelengths s
      let P := scalarWilsonBank d h tag u a Z O
      (∀ j ≤ r, P j = ∑ t, tensorWeight Y s v t *
        scalarWilsonBank d h tag u a Z (L ∘ axisPayoff Y s t) j) ∧
      ∀ g > (0:ℝ), ‖d.conditioned (offset a g) O (expLinks G _ (g • u)) -
        peval P r g‖ ≤ K*g^(r+1) := by
  let F := fun t : AxisTuple Y s=> L ∘ axisPayoff Y s t
  have fact t := axes_witnessed Y s t L
  obtain ⟨K,hK,buy⟩ := uniform_test_bank d hZ h tag u a F
    (fun t=>L.continuous.comp (fact t).1) (fun t k U=>congrArg L ((fact t).2.1 k U))
    (fun t=>(fact t).2.2) r
  refine ⟨K,hK,?_⟩
  intro v bound O P
  have eqn : O = fun U => ∑ t,tensorWeight Y s v t * F t U := by
    funext U
    change L (fullProduct (retest Y v).wavelengths s U) = _
    rw [tested_product_axes,map_sum]
    apply sum_congr rfl
    intro t _
    exact L.map_smul _ _
  dsimp only [P]
  rw [eqn]
  exact buy (tensorWeight Y s v) (tensorWeight_bounded Y s v bound)
end YM.Integration.FVA1Physical.Round2
