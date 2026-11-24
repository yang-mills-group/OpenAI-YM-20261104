import YM.Integration.WilsonCoherentMayerOldSlots

/-! A paid complex regular row can be tested by a real contraction on the same
old representative and entered in its existing marked budget. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonCoherentMayerOldProjection


open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical


open WilsonCoherentMayerOldSlots AnalyticBridge.VerifiedReset
variable {G:Gauge} {f:Side} (A:Rep G f) (a:RegularAddress f) (F:Config G f→ℂ)
    (χ:ℂ→L[ℝ]ℝ) (contract:∀z,|χ z|≤‖z‖) {u:ℝ}
    (smooth:A.p.Regular a.support F) (paid:A.p.supBounds a.site a.support F u)

include smooth in
theorem regular:A.p.Regular a.support (fun U=>χ (F U)):=regular_mapped χ smooth

include contract smooth paid in
theorem price:A.p.supBounds a.site a.support (fun U=>χ (F U)) u:=by
  refine ⟨paid.1,fun U ht w hw hp=>?_⟩
  change ‖leftDerivs (⇑χ ∘ F) _ _‖≤_
  rw [Push.Local.left_linear χ w (smooth.smooth U ht) hw,Real.norm_eq_abs]
  exact (contract _).trans (paid.2 U ht w hw hp)

variable (old:Team (QLocalInheritedRegularSlots.carrier A))

include smooth paid contract in
theorem seated:
    ∃(W:Team (QLocalInheritedRegularSlots.carrier A))(b:Leaf (QLocalInheritedRegularSlots.carrier A)),
      old.own⊆W.own ∧ b∈W.own ∧ W.weight=old.weight*u ∧ b.crest=a.support ∧
      ∀U,b.ingredient U=masked A.p.threshold a.support (fun V=>χ (F V)) U:=by
  obtain ⟨tag,unused⟩:=room A a old
  let landed:=fun U=>χ (F U)
  have legible:=regular A a F χ smooth
  have budget:=price A a F χ contract smooth paid
  let W:=booked A a old tag unused landed legible budget
  let b:=ManuscriptQLocalOrdinaryLeaf.leaf A a landed legible budget tag
  have result:=entered A a old tag unused landed legible budget
  exact ⟨W,b,result.2.1,result.1,result.2.2.1,result.2.2.2.1,result.2.2.2.2⟩

end YM.Integration.WilsonCoherentMayerOldProjection
