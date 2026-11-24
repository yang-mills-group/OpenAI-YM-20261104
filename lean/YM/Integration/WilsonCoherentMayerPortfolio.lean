import YM.Integration.WilsonCoherentMayerDecorated
import YM.Integration.WilsonCoherentMayerSlots
import YM.Integration.ManuscriptQLocalMayerSum

/-! The quoted expense of the actual remaining signed Mayer cofactor once
the submitted ordinary marks have been separated at their original addresses. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPortfolio
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat.Legato WilsonCoherentMayerGate WilsonCoherentMayerSubmission
open WilsonCoherentMayerSignedCharge (polynomial residual)
open scoped Classical BigOperators
variable {G:Gauge} (run:Run G) {I:Type} [Fintype I] (d:I→ℕ)
variable {c f L:Side}{S:StepData c f}{T:Tube G S}{F:Forest S.ratio}{R:Rep G f}
    {P:Teller G}{Q:ConnectedActivityE6.Target G P}{W s μ C:ℝ}{o:Target.Order G W}
    {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi}
    {q r a b Y D' v C' A B cost K θ δ ζ α:ℝ} {p:Molecule S}
    (N:Captain H j C' D' v Y A b r B q n χ)
    (law:Awning H N.conduit A b cost a δ ζ k l) (room:Q.goal L s≤K) (allow:Mayer.Approved K θ j M)
    (entry:Submitted run R I) (old:Team R) (fresh:∀m∈old.own,∀i,m.turn≠(row entry i).turn)
local notation "prior" => together entry old fresh
local notation "kept" => team prior (occupied entry)
local notation "other" => p\Team.signs prior S
variable (before:(prior).signs S⊆p) (cohort:Mayer.Start other)
    (reserve:(M+4:ℝ)*r≤α) (charge:1≤α) (speed:ζ≤α) (inside:authorized H p)
    {ρ:ℝ} (radius:1≤ρ) (small:ρ*Q.goal L s≤1)

include allow radius small in
theorem account (entered:Team R) (fits:entered.signs S⊆p) (start:Mayer.Start (p\entered.signs S)):
    (∑u:Mayer.Decors (p\entered.signs S) M,(entered.weight*
      ∏i:↥(p\entered.signs S),θ*(N.conduit.tag i.val)^((u i).val+1))*ρ^Mayer.decorOrder u) ≤
    entered.weight*(∏i∈p\entered.signs S,N.conduit.fare i)*Mayer.spreadRate M θ ρ^p.card:=by
  have heads:(∏i∈p\(p\entered.signs S),Laminate.coverWeight entered S i)=entered.weight:=by
    rw [Laminate.compartments entered p fits,Laminate.coverTotal]
  have result:=(ManuscriptQLocalMayerSum.signed_team (Ξ:=N.conduit) entered p allow radius small fits start).2
  simpa only [ManuscriptQLocalMayerSum.decorated,Mayer.tariff,heads] using result

end YM.Integration.WilsonCoherentMayerPortfolio
