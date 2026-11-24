import YM.Integration.WilsonMovingFiniteConditional
import YM.Integration.WilsonMovingFiniteAction
import YM.Integration.WilsonRunFormalMarkedStep
import YM.Integration.WilsonMarkedFiniteWickDefect

/-! Numerical finite evaluation of the entire independent marked cubature on
the selected run, with the true old potential and all translated test cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRunFiniteWickCubature
open FormalBulk08 Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision Stationary Lotus Shore
open Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G : Gauge} {K : KernelChoices} {D j t : ℕ}
    (P : Flight j t) (L : Lodge P.patch) (W : Pot G) (ρ : ChartRatio G)
    (b : P.patch.Branches K G) (block : 2≤P.L.val)

def ledger (Y : Anthem D G) (h l : ℕ) (f : Dawn.Studio D) (n : Side)
    (tag : (primary P.patch K n).Choices) (y : Rays (wire G n)) : PowerSeries ℝ :=
  let F := Reef.floor K P L n
  let H := Reef.ferry P b L n
  let U := Reef.flush F tag ρ (Mesa.stone W _)
  PowerSeries.C (Kemp.aven P.L h) * ∑ x : Site P.L,
    WilsonConditionalTaylorWick.quotient (WilsonMovingFiniteConditional.lift (wire G n) _)
      (WilsonMovingFiniteConditional.mean H y) H.saddle.q (WilsonMovingFiniteConditional.interaction U)
      (Reef.seat F (Kemp.resite (wrap _ (lift x)) (Kemp.banner l (Y (Dawn.throughW x D block f)) _)))

theorem observed (Y : Anthem D G) (h l : ℕ) (f : Dawn.Studio D) (n : Side)
    (tag : (primary P.patch K n).Choices) (y : Rays (wire G n))
    (ratio : LocalRatio ρ) (order : 4≤t) (ready : Story W (pink K.penalty P.wing)) :
    glimpse y (WilsonFormalMarkedCubature.finiteTransfer P L W ρ b block Y h l f n tag) =
      ledger P L W ρ b block Y h l f n tag y := by
  obtain ⟨v,B,hv,hB,stock,-⟩ := colors G K.penalty K.penalty_pos P.legal
  have lead := stoned_main hv.le hB.le (stock P.wing).1 ready.toVivid ready.ink (n*P.L)
  have solved := Reef.consolidate P ρ b L n ratio tag (Mesa.stone W _) lead order
  unfold WilsonFormalMarkedCubature.finiteTransfer ledger
  rw [map_mul,map_sum]
  have cost : glimpse y (PowerSeries.C (MvPolynomial.C (Kemp.aven P.L h))) = PowerSeries.C (Kemp.aven P.L h) := by
    simp [Jets.glimpse]
  rw [cost]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  exact WilsonMovingFiniteConditional.quotient _ y _ _ solved

variable {d e : ℕ} (R : Run G)
    (roofs : ∀ k, Lodge ((R.family.path.levels.clock.op k 0).patch)) (a : hue G) (fit : d<e)

theorem onRun (simple : G.Simple) (N i per : ℕ) (hi : i<N)
    (z : Letter (R.family.labels.level d)) (l : ℕ) (f : Dawn.Studio e)
    (tag : (primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel
      (R.family.S.side i per)).Choices) (y : Rays (wire G (R.family.S.side i per))) :
    let V := R.family.path.levels
    let P := destination V N i
    let bs := fun k => (V.blocks k 0).branches
    let W := Dove.model V roofs bs R.metals.O a N (i+1)
    let Y := (WilsonRunFormalMarkedStep.graph R roofs a fit N (i+1)) z
    let n := R.family.S.side i per
    glimpse y (WilsonFormalMarkedCubature.finiteTransfer P (roofs i) W R.metals.O (bs i)
      (Elm.growL V i) Y d l f n tag) =
      ledger P (roofs i) W R.metals.O (bs i) (Elm.growL V i) Y d l f n tag y := by
  intro V P bs W Y n
  apply observed
  · exact R.alloy.B.ratio
  · exact V.clock.adm i
  · exact (Dove.genu V roofs bs R.metals.O a R.alloy.B.ratio simple (i:=i+1) (N:=N) hi).toStory

end YM.Integration.WilsonRunFiniteWickCubature
end
