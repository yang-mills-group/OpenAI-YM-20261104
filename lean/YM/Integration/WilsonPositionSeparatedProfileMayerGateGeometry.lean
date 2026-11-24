import YM.Integration.WilsonPositionSeparatedProfileMayerGateSafety
import YM.Integration.WilsonCoherentMayerSlots
import YM.Extra.ITERATION_NO_LOSS.Geometry
import YM.Extra.WILSON_STARTUP.Face

/-! The original zero-sector mask warning costs only the fixed submitted
stencils, independently of the large torus and the forest. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileMayerGateGeometry
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Legato
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio} {R:Rep G f}
    {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W}
    {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi}

open WilsonCoherentMayerSubmission WilsonCoherentMayerSlots WilsonPositionSeparatedProfileMayerGateSafety
variable {run:Run G} {I:Type} [Fintype I] (entry:Submitted run R I)

theorem located (T:Tube G S) (s:ℝ) : sites entry T s ⊆ univ.biUnion fun i:I=>
    halo 10 (((R.activities.reg (entry.key i)).support).image S.ratio.parent):=by
  intro a ha
  obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp ha
  apply Finset.mem_biUnion.mpr;refine ⟨i,mem_univ i,?_⟩
  apply halo_spec.mpr
  rcases Finset.mem_union.mp hi with touched|anchored
  · obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp touched
    obtain ⟨x,hx,hit⟩:=(Finset.mem_filter.mp hp).2
    have near:=Work.E04.parent_separation S.ratio x p.1
    have fine:=WilsonStartup.visit_near p hit
    exact ⟨_,Finset.mem_image.mpr ⟨x,hx,rfl⟩,by omega⟩
  obtain ⟨e,he,rfl⟩:=Finset.mem_image.mp anchored
  obtain ⟨b,hb,ends⟩:=Finset.not_disjoint_iff.mp (Finset.mem_filter.mp he).2
  rw [Wing.badge_area] at hb
  obtain ⟨u,hu,d0⟩:=halo_spec.mp hb
  obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hu
  obtain ⟨x,hx,near⟩:=Extra.Iteration.Shapes.inspect_dist _ hv
  refine ⟨_,Finset.mem_image.mpr ⟨x,hx,rfl⟩,?_⟩
  have parents:=Work.E04.parent_separation S.ratio x v
  rw [separation_comm x v] at parents
  have step:separation b (atEdge S e)≤1:=stride e ends
  have first:=separation_triangle (S.ratio.parent x) (S.ratio.parent v) b
  have last:=separation_triangle (S.ratio.parent x) b (atEdge S e)
  simp only [Nat.zero_mul] at d0
  omega

theorem count (T:Tube G S) (s:ℝ): (sites entry T s).card≤
    ∑i:I,(R.activities.reg (entry.key i)).support.card*21^4:=by
  refine (Finset.card_le_card (located entry T s)).trans (Finset.card_biUnion_le.trans ?_)
  apply Finset.sum_le_sum;intro i _
  exact (Lattice.Corona.halo_size _ 10).trans (Nat.mul_le_mul_right _ Finset.card_image_le)

theorem submitted (old:Team R) (shelf:Shelf R) (d:I→ℕ) (x:I→Site f)
    (y:(i:I) → run.family.label (d i)) (phase:I→ℂ→L[ℝ]ℝ) (T:Tube G S) (s:ℝ) :
    (sites (issued run d x old shelf y phase) T s).card≤∑i:I,(run.family.localSection (d i)).stencil.card*21^4:=by
  refine (count (issued run d x old shelf y phase) T s).trans ?_
  apply Finset.sum_le_sum;intro i _;apply Nat.mul_le_mul_right
  change (R.activities.reg (key run d x old i)).support.card≤_
  unfold key;rw [(shelf _ _).1];exact Finset.card_image_le

end YM.Integration.WilsonPositionSeparatedProfileMayerGateGeometry
