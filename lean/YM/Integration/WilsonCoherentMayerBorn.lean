import YM.Integration.WilsonCoherentMayerResources
import YM.Integration.WilsonCoherentMayerSubmission
import YM.Integration.WilsonRetainedSignedStencilPhysical

/-! The quoted expense of the actual remaining signed Mayer cofactor once
the submitted ordinary marks have been separated at their original addresses. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerBorn
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

open WilsonCoherentMayerSubmission PhysicalNext.Repeat.Legato
variable {run:Run G} {I:Type} [Fintype I] (entry:Submitted run R I)

include H in
theorem sample (X:Coat T F) (hx:X.x=s) (hm:X.manifest) (hot:0<R.beta) (z:momentSpace X):
    (∏m∈occupied entry,read entry m (WilsonCoherentMayerOccurrences.field R X z))=
    WilsonRetainedSignedStencilPhysical.marked run entry.grade entry.phase R.p.threshold
      entry.label entry.site X R.beta z (Coat.gStep R.beta):=by
  rw [full,WilsonRetainedSignedStencilPhysical.actual _ _ _ _ _ _ _ hot]
  have roomY:Room P S T (X.wrapY z.1).x:= hx.symm ▸ H.laws.data.room
  have same:=Vine.shine (X.wrapY z.1) roomY hm R.beta z.2
  unfold WilsonCoherentMayerOccurrences.field
  rw [same]

include law room allow
theorem earned (old:Team R) (fresh:∀m∈old.own,∀i,m.turn≠(row entry i).turn)
    (before:(together entry old fresh).signs S⊆p)
    (u:Mayer.Decors (p\(together entry old fresh).signs S) M) (hw:Mayer.decorOrder u≤M)
    (cohort:Mayer.Start (p\(together entry old fresh).signs S)) (reserve:(M+4:ℝ)*r≤α) (charge:1≤α)
    (speed:ζ≤α) (inside:authorized H p)
    (X:Coat T F) (healthy:Healthy (Pressure.temp s) (H.unionP p) X.V)
    (hx:X.x=s) (hk:X.width=o.K) (hχ:X.χ=χ) (hm:X.manifest) (hot:0<R.beta) :
    let prior:=together entry old fresh
    let kept:=team prior (occupied entry)
    let rem:=Mayer.planned H p u (Laminate.partner kept H) X
    Measurable rem ∧ ∀z,
      Mayer.planned H p u (Laminate.partner prior H) X z=
        WilsonRetainedSignedStencilPhysical.marked run entry.grade entry.phase R.p.threshold
          entry.label entry.site X R.beta z (Coat.gStep R.beta)*rem z ∧
      |rem z|≤(X.catastrophe (o.ξ/2) R.beta (blaze p)).indicator
         (fun _=>old.weight*∏i:↥(p\prior.signs S),θ*(N.conduit.tag i.val)^((u i).val+1)) z.2:=by
  let prior:=together entry old fresh
  let kept:=team prior (occupied entry)
  have entered:=registered entry old fresh
  have forSale:∀i∈p\(p\prior.signs S),Fits H (Laminate.partner kept H i) (H.supportP i) j:=by
    intro i hi
    rw [Laminate.compartments prior p before,←census prior (occupied entry) S] at hi
    exact (Laminate.partnerFit (M:=kept) (H:=H) hi).1
  refine ⟨(WilsonCoherentMayerMultiplier.earned u Finset.sdiff_subset hw N law room allow
    (Laminate.partner kept H) forSale cohort X healthy hx hk hχ hm).1,fun z=>?_⟩
  have both:=WilsonCoherentMayerCofactor.funded N law room allow prior (occupied entry) entered.1
    (regular entry) (read entry) (qualifies entry) before u hw cohort reserve charge speed inside X healthy hx hk hχ hm z
  rw [sample (H:=H) entry X hx hm hot z] at both
  exact ⟨both.1,by simpa only [prior,entered.2,Team.weight] using both.2⟩

end YM.Integration.WilsonCoherentMayerBorn
