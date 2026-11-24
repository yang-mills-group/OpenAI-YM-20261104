import YM.LocalLTE.Tile.Share
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Fir
/-! Local LTE high-order representation/compatibility on supported tiles. Adapts
`PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Fir`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {J₀ M D' j m: ℕ} {K : Teller G} {p a W U V g : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi}
local notation "B" => radiusB p
open Brim Height Refrain
variable (X' : Match.Alliance I H 1 0) (p' : BudgetPoint)
variable (γ : ℝ)
def hKeepN (J₀ t : ℕ) (z:Magazine I) := if z∈Meadow.bouquetN I J₀ t then 0 else opus I X' χ γ z

def timbresN (J₀ t:ℕ): Collection.Source G c:= ⟨choir (hKeepN X' (χ:=χ) γ J₀ t) ∘ pennant I, fuse I X' χ ∘ Refrain.badge I⟩

lemma compassN (k:ℕ) (x: ℕ) : (timbresN X' (χ:=χ) γ J₀ k|>.logRead x) = (if (pennant I x).2 ∈ Meadow.bouquetN I J₀ k then 0 else (plusone I X' χ γ).logRead x):= by
  unfold timbresN plusone choir; let y:= Song.pennant I x; change Rim c • ((if _ then (_:Config G c→ℝ) else _) ∘ y.1.view)= _; split
  · ext; simp
  rfl

end YM.PhysicalNext.Repeat.Meadow
