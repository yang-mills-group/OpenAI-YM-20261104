import YM.Integration.WilsonCoherentMayerCofactor

/-! The quoted expense of the actual remaining signed Mayer cofactor once
the submitted ordinary marks have been separated at their original addresses. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerResources
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio}
  {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W}
  {R:Rep G f} {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi}
  {q r a b D v Y C' A B cost K θ δ ζ α:ℝ} {p select:Molecule S}
  (N:Captain H j C' D v Y A b r B q n χ)
  (law:Awning H N.conduit A b cost a δ ζ k l) (room:Q.goal L s≤K)
  (allow:Mayer.Approved K θ j M)

open WilsonCoherentMayerGate

theorem original {Ξ:Utopia H j v D r C' χ} (prior:Team R) (chosen:Finset (Leaf R)) (enrolled:chosen⊆prior.own)
    (ordinary:∀m∈chosen,∃i,m.turn=.logKey i)
    (before:prior.signs S⊆p) (u:Mayer.Decors (p\prior.signs S) M) :
    Mayer.tariff Ξ p θ u (Laminate.coverWeight prior S)=
      (∏m∈chosen,m.weight)*Mayer.tariff Ξ p θ u (Laminate.coverWeight (team prior chosen) S) :=by
  have remaining:(p\(p\prior.signs S))=prior.signs S:=Laminate.compartments prior p before
  have kept : (∏i∈prior.signs S, Laminate.coverWeight (team prior chosen) S i)=
      ∏m∈prior.own\chosen,m.weight :=by
    calc
      _ = ∏i∈(team prior chosen).signs S,Laminate.coverWeight (team prior chosen) S i :=
        Finset.prod_congr (census prior chosen S).symm (fun _ _=>rfl)
      _ = _ := (Laminate.coverTotal _ S).trans (WilsonCoherentMayerCofactor.capital prior chosen enrolled ordinary)
  unfold Mayer.tariff
  rw [remaining,Laminate.coverTotal,kept]
  unfold Team.weight
  rw [←Finset.prod_sdiff enrolled]
  ring

end YM.Integration.WilsonCoherentMayerResources
