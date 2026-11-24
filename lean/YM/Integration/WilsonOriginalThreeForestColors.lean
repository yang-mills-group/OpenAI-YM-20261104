import YM.Integration.WilsonOriginalThreeCopiedCharts
/-! The three compact colors use the same physical forest field at each value of the coupling. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalThreeForestColors
open Function Finset Lattice RG Wilson Marker Gauge QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Affinity
open Comparison.RG02 AllOrder.Floe Multi Exterior Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open Precision Tree WilsonOriginalPointCompactRoster WilsonOriginalOccupiedFieldLayout WilsonEmittedRootedJetWage
open WilsonOriginalThreeCopiedCharts WilsonOriginalPinnedGradedPeek PhysicalForestAction PhysicalForestRay PhysicalForestMarkedRay
open Filter Matrix Stationary Next.SectorChange FreeResolvent MeasureTheory
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open scoped Classical BigOperators
variable {G:Gauge} {n N c:Side} {I:Type} [Fintype I] {q:ℕ} {σ:ℝ}
  (owner:I→Fin 3) (grades:Fin 3→ℕ) (sites:Fin 3→Site n)
  (T:(i:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner i)) q σ) (A:Fin 3→Set ℂ) (charge:I→ℂ)
  (h:n.val∣N.val) (t:Wallet A) (L:Layout G) (tape:Finset Age)
local notation "M" => rows owner grades sites T A charge
local notation "J" => Stock.census (Fin 3)
private theorem angular (u:Link G N):mantle u=RG.increment 1 (edgeColor u):=by
  rw [←Mosaic.mantle_input]
  funext e
  change input G N u e=G.lieExp (edgeColor u e)*1
  rw [input_color,mul_one]

variable (S:StepData c N) (F:Forest S.ratio) {p:Clip} {P:PathData G} {O:ChartRatio G}
  (K:Bulk.Kernel S p P O) (D:Matrix (Woods G N) (Woods G c) ℝ) (x:fieldDir G c 1) (z:Key F G→ℝ)
theorem original {w:Fin 3→ℝ}{σ₀ C:ℝ}{d seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ₀ C d seats shelf) (σpos:0<σ₀) (hs:0<σ) (bounded:∀v a,a∈A v→‖a‖≤1)
    (s:Hot (J)) (g:ℝ):
    chartMark S F D K x z (copyColor h M grades (fun a=>(M a).paint t) L tape) s g=
      ∑i:I,if (J).fire (owner i)=s.val then charge i*chartMark S F D K x z
        (bank owner grades sites T A h t L tape i) name g else 0:=by
  simp only [chartMark,PhysicalForestAction.field,angular]
  exact held owner grades sites T A charge h t L tape stock σpos hs bounded s (g,_)

end YM.Integration.WilsonOriginalThreeForestColors
