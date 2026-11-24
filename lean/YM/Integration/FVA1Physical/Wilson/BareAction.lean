import YM.Integration.FVA1Physical.Wilson.CommonChart
import YM.Comparison.RG02.Bare.View

/-! The Wilson bare correction from the accepted qlocal chain cancels the
whole inherited main action. The chain's initial loop vanishes. After the
replica chart change, the sole remaining term in the unmarked action is the
actual Haar logarithm of the relative coordinates. -/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.Wilson

open Filter YM.Lattice YM.RG YM.Tree YM.Precision YM.Exterior
open YM.Comparison.RG02 YM.FVA2.CityHistory
open scoped Topology BigOperators Classical

variable {G : Gauge} {H : History G} (Y : Bulk.Chain H) (i p : ℕ)
    {V : Type} [DecidableEq V] (R : Marker.Census V)
local notation "St" => H.levels.clock.op i p
local notation "Cn" => H.S.side i p
local notation "Fn" => H.S.side (i+1) p
local notation "K" => Y.step (i+1) i p (Nat.lt_succ_self i)

theorem top_action_germ (F : Forest (St).ratio) (t : (St).Choices)
    (W : Bulk.Colors R G Fn) :
    (fun w : ℝ × (Future G St F × Pins G Cn) =>
      Bulk.geometric K F t (Bare.bareUp R i p (H := H) W) (w.1, axesP G Cn w.2.2, w.2.1))
      =ᶠ[𝓝 0] fun w => Spot.heat St F t (absoluteFree F w.2, w.2.2) -
        w.1 ^ 2 * Real.log (∏ j, Y.O.J (w.2.1 j)) := by
  filter_upwards [full_action_residual F K t (Bare.bareUp R i p (H := H) W)] with w hw
  let x := axesP G Cn w.2.2
  let a := w.2.1
  let U := Work.F03.live F (x, a)
  let P := H.rep (i+1) p (i+1)
  let A := Bulk.geometric K F t (Bare.bareUp R i p (H := H) W) (w.1, x, a)
  let B := Spot.heat St F t (absoluteFree F w.2, w.2.2)
  let J := Real.log (∏ j, Y.O.J (a j))
  change A - B = mainTerm P.clip P.path U - YM.Wilson.energy U + w.1 ^ 2 * (loop P.path U - J) +
    (YM.Wilson.energy U - mainTerm P.clip P.path U) at hw
  have hz : loop P.path U = 0 := Bare.no_loop Y i p U
  rw [hz] at hw
  change A = B - w.1 ^ 2 * J
  linear_combination hw

end YM.Integration.FVA1Physical.Wilson

