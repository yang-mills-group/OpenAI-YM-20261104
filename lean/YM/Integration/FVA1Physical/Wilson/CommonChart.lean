import YM.FVA2.FundingOffer
import YM.Integration.LocalFormalCoefficients
import YM.Work.F05.Measure

/-! The FVA2 bare full-period action and the qlocal action on the same forest,
branch and coarse field. The logarithmic change of free-link coordinates
absorbs precisely the coarse replica. The action identity leaves the entire
inherited action, loop, Haar and source-supplement discrepancy visible. -/

noncomputable section

namespace YM.Integration.FVA1Physical.Wilson

open Filter Function MeasureTheory Set
open YM.Lattice YM.RG YM.Tree YM.Exterior YM.Precision
open YM.PertExtension.Chart YM.FVA2.CityHistory
open YM.Comparison.RG02 YM.Push.BetaTransport
open scoped Topology BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio)

/-- Absolute free-link logarithms for the qlocal relative chart on this forest. -/
def absoluteFree (v : Future G S F × Pins G c) : Future G S F :=
  fun i => G.plog (G.mat (Work.F05.exposure F (axesP G c v.2) v.1 i))

/-- The same link configuration in both charts on a joint neighborhood of
zero in the free and coarse directions. -/
theorem exponential_absoluteFree :
    ∀ᶠ v : Future G S F × Pins G c in 𝓝 0,
      expLinks G F.Free (absoluteFree F v) = Work.F05.exposure F (axesP G c v.2) v.1 := by
  let L := fun v : Future G S F × Pins G c => (axesP G c v.2, v.1)
  have hL : Continuous L := ((axesP G c).continuous.comp continuous_snd).prodMk continuous_fst
  have hX := ((Work.F05.exposure_continuous (G := G) F).comp hL).tendsto 0
  have h0 : uncurry (Work.F05.exposure F (G := G)) (L 0) = 1 := by
    simpa [L] using Work.F05.exposure_zero (G := G) F
  rw [Function.comp_apply, h0] at hX
  have hi (i : F.Free) := (tendsto_pi_nhds.mp hX i).eventually G.plog_right
  filter_upwards [eventually_all.mpr hi] with v hv
  exact funext (fun i => hv i)

/-- The FVA2 bare energy, including its conditional block penalty, pulled
back to the relative chart used in the canonical qlocal kernel. -/
theorem bare_action_germ (t : S.Choices) :
    (fun v : Future G S F × Pins G c => Spot.heat S F t (absoluteFree F v, v.2)) =ᶠ[𝓝 0]
      fun v =>
        let x := axesP G c v.2
        let U := Work.F03.live F (x, v.1)
        YM.Wilson.energy U + noiseTaylor S (represent x) U t := by
  filter_upwards [exponential_absoluteFree (G := G) F] with v hv
  rw [Spot.finance, hv, Work.F05.drape_exposure, ← direct_link]
  simp only [Work.F03.live, tagEnergy, noiseEnergy, linkEnergy, noiseTaylor, Finset.mul_sum]

/-- The coordinate change cancels the entire common bare action and block
penalty. The remaining terms are the actual incoming local action discrepancy,
loop, logarithmic Haar ratio and marked-color vacuum supplement. -/
theorem full_action_residual {p : Clip} {P : PathData G} {O : ChartRatio G}
    {V : Type} [DecidableEq V] {R : Marker.Census V}
    (K : Bulk.Kernel S p P O) (t : S.Choices) (W : Bulk.Colors R G f) :
    (fun w : ℝ × (Future G S F × Pins G c) =>
      Bulk.geometric K F t W (w.1, axesP G c w.2.2, w.2.1) -
        Spot.heat S F t (absoluteFree F w.2, w.2.2)) =ᶠ[𝓝 0]
      fun w =>
        let x := axesP G c w.2.2
        let a := w.2.1
        let U := Work.F03.live F (x, a)
        mainTerm p P U - YM.Wilson.energy U +
          w.1 ^ 2 * (loop P U - Real.log (∏ i, O.J (a i))) +
          Bulk.supplement S F W (w.1, x, a) := by
  have h := (continuous_snd.tendsto (0 : ℝ × (Future G S F × Pins G c))).eventually
    (bare_action_germ (G := G) F t)
  filter_upwards [h] with w hw
  rw [hw]
  unfold Bulk.geometric Bulk.stone Bulk.fee Bulk.pillar Bulk.officer
  let a := w.2.1
  let x := axesP G c w.2.2
  let U := Work.F03.live F (x, a)
  change (mainTerm p P U + noiseTaylor S (represent x) U t +
    (w.1 ^ 2 * (loop P U - Real.log (∏ i, O.J (a i))) + Bulk.supplement S F W (w.1, x, a))) -
    (YM.Wilson.energy U + noiseTaylor S (represent x) U t) =
    mainTerm p P U - YM.Wilson.energy U + w.1 ^ 2 * (loop P U - Real.log (∏ i, O.J (a i))) +
      Bulk.supplement S F W (w.1, x, a)
  ring

/-- The absolute-coordinate image carries the exact Haar density of relative
coordinates for every compact chart test and every admitted coarse field in
one common neighborhood. In particular the density includes every free link. -/
theorem compact_haar {Z : ChartRatio G} (hZ : LocalRatio Z) :
    ∃ U ∈ 𝓝 (0 : Future G S F × Pins G c),
      ∀ (u : Pins G c) (A : Set (Future G S F)), IsCompact A →
        A ⊆ Work.F05.parcel F Z → (∀ a ∈ A, (a, u) ∈ U) →
        F.order G ((fun a => expLinks G F.Free (absoluteFree F (a, u))) '' A) =
          ∫⁻ a in A, ENNReal.ofReal (Work.F05.load F Z a) := by
  let U := {v : Future G S F × Pins G c |
    expLinks G F.Free (absoluteFree F v) = Work.F05.exposure F (axesP G c v.2) v.1}
  refine ⟨U, exponential_absoluteFree (G := G) F, ?_⟩
  intro u A hA hpatch hU
  have images : (fun a => expLinks G F.Free (absoluteFree F (a, u))) '' A =
      Work.F05.exposure F (axesP G c u) '' A :=
    Set.image_congr fun a ha => hU a ha
  rw [images]
  exact Work.F05.order_exposed F hZ (axesP G c u) A hA hpatch

end YM.Integration.FVA1Physical.Wilson

