import YM.Integration.WilsonCoherentMayerGate

/-! Exact single removal of the submitted marked occurrences from the actual
Mayer integrand. Its non-marked factors, eligibility, anchors, and the common
Gaussian sample remain in the original signed molecule. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerOccurrences
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
open WilsonCoherentMayerGate

def field (R:Rep G f) (X:Coat T F) (z:momentSpace X) : Config G f :=
  let Y:=X.wrapY z.1
  Y.input (worldZ Y R.beta z.2)

def anchor (R:Rep G f) (a:ℝ) (w:Wing) (X:Coat T F) (z:momentSpace X) : ℝ :=
  let Y:=X.wrapY z.1
  Y.enforce (2*a) (worldZ Y R.beta z.2) (Y.plaza (areas R T 0 Y.B (w.badge S)))

theorem leaf (prior:Team R) (m:Leaf R) (live:m∈prior.own) (X:Coat T F) (z:momentSpace X) :
    (Laminate.partner prior H (m.turn.badge S)).joint X z=
      m.ingredient (field R X z)*anchor R o.a m.turn X z :=by
  unfold Insert.joint Laminate.partner
  rw [Laminate.chosenAt prior S (Laminate.power H) _ m live]
  rfl

theorem removed (prior:Team R) (chosen:Finset (Leaf R)) (ordinary:∀m∈chosen,∃i,m.turn=.logKey i)
    (raw:Leaf R → Config G f → ℝ)
    (reading:∀m∈chosen,∀U,m.turn.qualifies R U→m.ingredient U=raw m U)
    (m:Leaf R) (live:m∈prior.own) (X:Coat T F) (z:momentSpace X) :
    (Laminate.partner prior H (m.turn.badge S)).joint X z=
      (if m∈chosen then raw m (field R X z) else 1)*
      (Laminate.partner (team prior chosen) H (m.turn.badge S)).joint X z :=by
  have enters : place chosen m∈(team prior chosen).own:=Finset.mem_image_of_mem _ live
  have restore:=leaf (H:=H) (team prior chosen) (place chosen m) enters X z
  rw [WilsonCoherentMayerGate.address] at restore
  rw [leaf prior m live,restore,WilsonCoherentMayerGate.source prior chosen ordinary raw reading live, mul_assoc]

theorem original (prior:Team R) (chosen:Finset (Leaf R)) (enrolled:chosen⊆prior.own)
    (ordinary:∀m∈chosen,∃i,m.turn=.logKey i) (raw:Leaf R → Config G f → ℝ)
    (reading:∀m∈chosen,∀U,m.turn.qualifies R U→m.ingredient U=raw m U)
    (before:prior.signs S⊆p) (u:Mayer.Decors (p\prior.signs S) M)
    (X:Coat T F) (z:momentSpace X) :
    Mayer.planned H p u (Laminate.partner prior H) X z=
      (∏m∈chosen,raw m (field R X z))*
        Mayer.planned H p u (Laminate.partner (team prior chosen) H) X z :=by
  let g (m:Leaf R):= if m∈chosen then raw m (field R X z) else 1
  have factors : (∏i∈prior.signs S,(Laminate.partner prior H i).joint X z)=
      (∏m∈prior.own,g m)*(∏i∈prior.signs S,(Laminate.partner (team prior chosen) H i).joint X z) :=by
    simp only [Team.signs,Finset.prod_image (Laminate.distinct prior S)]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun m hm=>removed prior chosen ordinary raw reading m hm X z
  have picked : (∏m∈prior.own,g m)=∏m∈chosen,raw m (field R X z) :=by
    rw [← Finset.prod_sdiff enrolled]
    have off : (∏m∈prior.own\chosen,g m)=1 :=Finset.prod_eq_one fun m hm=>if_neg (Finset.mem_sdiff.mp hm).2
    rw [off,one_mul]
    exact Finset.prod_congr rfl fun m hm=>if_pos hm
  unfold Mayer.planned
  rw [Laminate.compartments prior p before,factors,picked,mul_assoc]

end YM.Integration.WilsonCoherentMayerOccurrences
