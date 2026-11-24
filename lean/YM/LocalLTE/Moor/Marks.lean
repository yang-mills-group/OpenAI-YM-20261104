import YM.LocalLTE.Moor.Replica
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Trimmings
/-! Local LTE propagation: parameterized extension of Trio/Trimmings. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Trio
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C' F:Side} {J₀ j i m n W w r k l:ℕ} (B : BudgetPoint) {Y:Stars→Side}
section lo
variable {S:StepData c f} {K₀:Teller G} {d p a U T' : ℝ} {X: ConnectedActivityE6.Target G K₀} {o: Target.Order G p} {L:Side} {T:Tube G S} {R R': RG.Rep G f}
   {Z : Cash p d a L X o T' T R} {Z':Cash p d a L X o T' T R'}
    (Wt : Match.Alliance Z' Z 1 0) (γ:ℝ) (n:ℕ) (Q:∀ i:Stars,(Y i).val=2*(w+i.val)) (z:ℕ) (fa: ∀ i:Stars,Offer G (Y i))
    (u:Site c) (hq : ∀ i,B.Regular ((posting B Z').reg i).support ((plusone Z' Wt Chi.canonical γ).logRead i))
    (hP : ∀ i j, B.Regular univ (fa i j))
local notation "P" => (B)
local notation "P₀" => (Beam.marquee Z' B)
local notation "O" => Chi.canonical
local notation "h₀" => (plusone Z' Wt O γ)
local notation "h₁" => (Meadow.timbresN (J₀:=J₀) Wt (χ:=O) γ n)
local notation "R₀" => (Meadow.panelN Z' J₀ n)
local notation "D₀" => Meadow.studioN J₀ X.halo (radiusB d)
local notation "f₀" => (Meadow.baronyN Z J₀ O n γ)
include hq hP
lemma primN (hp:w+4 ≤z) (he:D₀ ≤ k) (hk : 2*z ≤ k) (hV : B.B=Pressure.radiusB d) : Tidy B (neighbors k u) (insightN B Wt γ n Q z fa J₀ u):= by
  let V i := Trio.unearned B Q z (rip fa) u i
  refine tidy_sub B (v:=V) (u:= Trio.earnedN B Wt γ n J₀ u - fun _ : Config G c=> f₀ u 1) ?_ ?_
  · apply tidy_sub _ _ (tidy_const ..)
    refine tidy_sum _ _ R₀ _ fun i hi=> ?_; by_cases hB: Meadow.garnerAt Z' B u i=0; · simp only [hB,zero_mul]; exact tidy_const ..
    refine tidy_scale _ _ (tidy_mask _ (X:=((P₀).reg i).support) ?_ ?_)
    · rw [Beam.rewrite_rule]; exact hq i
    intro j hj; apply (neighbors_mem ..).2; exact ((neighbors_mem ..).1 ((Meadow.assignedN Z' B u i hi hV hB).2 hj)).trans he
  refine tidy_sum _ _ _ _ fun i _=> tidy_scale _ _ (tidy_sum _ _ _ _ fun j _=> tidy_mask _ (unit_m B Q z fa hP hp (emerge Q i j u) i j) (patch Q z hp i j u hk)) -- pattern
end lo
end YM.PhysicalNext.Repeat.Trio
