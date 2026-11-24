import YM.RGComparison01.Marks.Emerson
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
variable (H:Cash W s μ L Q o C T R) (M:ι→ Lotus.Leaf R)(E:Ribbon R n)(P':BudgetPoint)
-- Recipe positions from persisted roots.User chooses before masks
structure Driver (M:ι→Lotus.Leaf R) where
   origin : ι→Site f
   admitted : Engaged M origin
namespace Driver
variable (D:Driver M)
local notation "o'"=> D.origin
/-- root selection deterministically. no permutation invariance at Y. -/
def main (p:Finset ι)(hp:p.Nonempty): ↥p:= ⟨hp.choose,hp.choose_spec⟩
def primary (D:Driver M) (S:StepData c f) (p:Finset ι): Site c:=if hp:p.Nonempty then S.ratio.parent (D.origin (main p hp)) else 0
abbrev soul (Z:ℕ)(p:Finset ι):= neighbors Z (primary M D S p)
-- acceptance set determined BEFORE testing.X.V. Canon not weighted yet. Opportunity for upstream to attach any other.We force zero outside.
def Quick (M:ι→Lotus.Leaf R) (E:Ribbon R n)(D:Driver M)(S:StepData c f)(m Y:ℕ)(p:Finset ι) := p.Nonempty ∧ p.card ≤ m ∧ ∀ i∈p, (∃ b:E.Node,(M i).turn=Wing.logKey b.val)∧ S.ratio.parent (D.origin i) ∈ neighbors Y (primary M D S p)
lemma full_card (S:StepData c f)(p:Finset ι)(hp:p.Nonempty): primary M D S p∈ (M (main p hp)).crest.image S.ratio.parent:= by unfold primary; rw [dif_pos hp]; exact mem_image_of_mem _ (D.admitted _)
-- not needing positivity. any all p larger.Pay whole for not.
variable {H M E}
lemma still {Z : Drawing.Count E H} {i:ι} {x: Head S}(hy : (Drawing.cabinet H E).ink Z=x) (he : Palette.sign M S i=x) : ∃ j:E.Node,(M i).turn=.logKey j.val:= by
   cases hx:(M i).turn with
   | logKey k=> rw [show Palette.sign M S i=(Wing.logKey k).badge S from congr_arg (fun t:Wing=>t.badge S) hx] at he
                have hv:= hy.trans he.symm; cases Z with
                | inl k=> exact ((Drawing.payer k.val _ (Sum.inl_injective (Sum.inr_injective (Sum.inr_injective hv)))).elim)
                | inr j=> exact ⟨j,Team.badged S (show (Wing.logKey k).badge S=(Wing.logKey j.val).badge S from hv.symm)⟩ -- wing.lens coercion
   | gasKey k=> have he' : (Drawing.cabinet H E).ink Z=(Wing.gasKey k).badge S:= hy.trans (he.symm.trans (congr_arg (fun t:Wing=>t.badge S) hx))
                unfold Cabinet.ink Wing.badge at he'; simp only [Function.Embedding.coeFn_mk, Sum.inr.injEq, Sum.inr_ne_inl] at he'
variable (H M E)
variable [Fintype ι]
lemma journeys (p:Finset ι)(hp:p.Nonempty){m Y:ℕ} (hc:p.card ≤ m) {z:Cl M H} (ht:z∈ledger M H (Drawing.cabinet H E) ℓ k p) (h:Cabinet.garage (Mint.width Q.halo (radiusB s) (radiusB s+n)) ℓ ≤ Y): Quick M E D S m Y p:= by
   let V:=Drawing.cabinet H E; have hx := (mem_filter.mp ht).2; refine ⟨hp,hc,fun i hi=> ⟨?_,?_⟩⟩
   · obtain ⟨k,hk,hx'⟩:= mem_biUnion.mp (show i∈ Stowe.recordSet M H z from hx.1.1.symm ▸ hi)
     have he := hx.2 k ((z.2 k).2.reaches_of hx')
     obtain ⟨⟨p',a⟩,hp,rfl⟩:= mem_map.mp (mem_filter.mp ht).1; obtain ⟨j,hj,hJ⟩:= mem_map.mp he
     exact Driver.still hJ rfl -- arg
   have hz : primary M D S p ∈ (M (main p hp)).crest.image S.ratio.parent:= full_card M D S p hp
   exact (neighbors_mem ..).mpr (((neighbors_mem ..).mp ((traits M H V p _ _ (main p hp|>.property) hz z ht).2 (Stowe.crest M H p z hx _ hi (mem_image_of_mem _ (D.admitted _))))).trans h)
end Driver
end Diner
end YM.RGComparison01.Pledge
