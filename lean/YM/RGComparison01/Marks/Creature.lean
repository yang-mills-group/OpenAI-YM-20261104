import YM.RGComparison01.Marks.Borders
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
namespace Diner
open Lanes Foreman Checks Baked Palette Pillow Resin Season Ink Heron Switch Mallow Ovens OmitClusters Song Refrain Motion Luggage Oceanic Extra.Iteration
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03 ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt Boulevard Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Divides Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera Slide
open Hoboken Stowe SliceRows
namespace Borders
open Driver
variable {i m Z k b:ℕ}
variable (M:ι→Lotus.Leaf R) (D:Driver M) (E:Ribbon R n)
variable [Fintype ι]
local notation "Zp"=> Diner.Driver.primary M D S
-- cumulative all roots at pre INTEGER exponent. λi/k_i comparison weights anchored, on PRIMARY ancestors (can pick first in crest). audience Mark. bounded. product keeps copies via temporary sold radii. need require works.Act.Model
variable (u:ι→ℝ) (V : Site c)
-- all anchors active retained.P.width
omit [Fintype ι] in
lemma creature (w Y:ℕ) (p:Finset ι) (hp: Quick M E D S w Y p)(H:Cash W s μ L Q o C T R) (j:ι) (hj:j∈p) :
  H.supportP (Palette.sign M S j) ⊆ neighbors (Y+2*Mint.width Q.halo (radiusB s) (radiusB s+n)) (Zp p) := by
  obtain ⟨⟨t,ht⟩,hF⟩:= hp.2.2 j hj
  have hx : Palette.sign M S j=(Drawing.cabinet H E).ink (.inr t):= by unfold Palette.sign; rw [ht]; rfl
  let c':= Drawing.cabinet H E; obtain ⟨hv,hh⟩:= c'.penned (.inr t)
  have he: S.ratio.parent (D.origin j)∈c'.foot (.inr t):= by change S.ratio.parent _∈ H.supportP ((Drawing.cabinet H E).ink _); rw [←hx]; exact Stowe.enrolled M H j (mem_image_of_mem _ (D.admitted _))
  rw [hx]; intro i hi; apply (neighbors_mem ..).2; let Y':=S.ratio.parent (D.origin j)
  apply (separation_triangle _ Y' _).trans; apply le_trans (Nat.add_le_add ((neighbors_mem ..).1 hF) ((separation_triangle _ (c'.site (.inr t)) i)))
  change _ ≤ Y+ (2*_); rw [separation_comm Y',two_mul]; exact Nat.add_le_add_left (Nat.add_le_add ((neighbors_mem ..).1 (hh he)) ((neighbors_mem ..).1 (hh hi))) _
end Borders
end Diner
end YM.RGComparison01.Pledge
