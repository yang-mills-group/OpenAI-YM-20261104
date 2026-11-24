import YM.Integration.WilsonPositionSeparatedProfileMayerFlat
import YM.LocalTaylorR2.Exponent.Gavel

/-! Each original support mask and each angular root factor equal one away
from a Gaussian warning over the actual plaquettes and root plaza. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileMayerGateSafety
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

open WilsonCoherentMayerSubmission WilsonCoherentMayerOccurrences
open LocalTaylorR2.Exponent
variable {run:Run G} {I:Type} [Fintype I] (entry:Submitted run R I)

/-- Origins of all plaquettes which can flag a submitted mark and of every
bond which can enter its attached cutoff, jointly before the forest or field. -/
def sites (T:Tube G S) (s:ℝ) : Support c := univ.biUnion fun i:I=>
  ((univ.filter fun p:Cell f=>∃v∈(R.activities.reg (entry.key i)).support,v∈RG.touched p).image
    (fun p=>S.ratio.parent p.1)) ∪
  ((univ.filter fun e:Bond f=>¬Disjoint (areas R T 0 (radiusB s) ((Wing.logKey (entry.key i)).badge S)) (ends S e)).image (atEdge S))

private theorem watchAt (X:Coat T F) (Y:Support c) (a:ℝ) (z:Air f G) (quiet:z∉eerie X Y a R.beta) {x:Site c} (hx:x∈Y) :
    X.watch x a R.beta X.B z:=by
  intro t ht
  exact atHome X Y a R.beta z quiet x hx t (by omega)

theorem clear (X:Coat T F) (H:Cash W X.x μ L Q o C T R) (fitted:X.width=o.K) (manifest:X.manifest) (flat:X.blank=X)
    (stamped:Stamp T) (y:F.Slice G) (z:Air f G) (quiet:z∉eerie X (sites entry T X.x) o.ξ R.beta) (i:I) :
    WilsonPositionSeparatedProfileMayerMasks.gates entry i o.a X (y,z)=1:=by
  let w:=Wing.logKey (entry.key i)
  let Y:=sites entry T X.x
  let U:=X.input (worldZ X R.beta z)
  have info:=H.laws.data
  have temp:0<X.t:=info.room.fiery
  have lower:=info.safety.2.2.2 F X rfl fitted manifest
  have hc:=WilsonPositionSeparatedProfileMayerFlat.fields (R:=R) info.funds.funds X flat y z o.a w
  have hc0:=WilsonPositionSeparatedProfileMayerFlat.fields (R:=R) info.funds.funds X flat X.Y z o.a w
  have useField:field R X (y,z)=U:=hc.1.trans hc0.1.symm
  have useRoot:anchor R o.a w X (y,z)=X.enforce (2*o.a) (worldZ X R.beta z) (X.plaza (areas R T 0 X.B (w.badge S))):=hc.2.trans hc0.2.symm
  have healthy:Healthy R.p.threshold (R.activities.reg (entry.key i)).support U:=by
    apply Finset.disjoint_left.mpr
    intro v live flagged
    obtain ⟨p,touches,excess⟩:=(RG.flags_spec _ _ _).mp flagged
    have hx:S.ratio.parent p.1∈Y:=by
      apply Finset.mem_biUnion.mpr
      exact ⟨i,mem_univ _,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨mem_univ _,v,live,touches⟩,rfl⟩)⟩
    have old:=X.blank_no (S.ratio.parent p.1) (30*X.B)
    rw [flat] at old
    have h:=(lower.2 stamped (S.ratio.parent p.1) old R.beta H.laws.intake.positive z (watchAt X Y o.ξ z quiet hx)).2.1 p rfl
    rw [shine X info.room manifest] at h
    rw [H.laws.intake.received.temp] at excess
    change X.t<toll U p at excess
    change toll U p<X.t/4 at h
    linarith
  unfold WilsonPositionSeparatedProfileMayerMasks.gates
  rw [useField,if_pos healthy]
  change anchor R o.a w X (y,z)=1
  rw [useRoot]
  apply Finset.prod_eq_one
  intro e he
  have hx:atEdge S e∈Y:=by
    apply Finset.mem_biUnion.mpr
    exact ⟨i,mem_univ _,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨mem_univ _,(Finset.mem_filter.mp he).2.2⟩,rfl⟩)⟩
  have bounded:‖(worldZ X R.beta z) e‖≤o.a*X.t:=by
    rw [←shine X info.room manifest]
    have h:=(X.watch_bonds (atEdge S e) temp o.rare.le H.laws.intake.positive (watchAt X Y o.ξ z quiet hx) e (by rw [separation_self];omega) (lower.1 e)).2
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith [info.safety.2.2.1,info.safety.2.1]) temp.le)
  by_contra missed
  have cut:=X.χ.exterior_gt ‖(worldZ X R.beta z) e‖ ((2*o.a)*X.t) (norm_nonneg _) (by have h:=o.large;positivity)
    (sub_ne_zero.mpr (Ne.symm missed))
  nlinarith [mul_pos o.large temp]

/-- One rate is chosen before all regulators, forests and locations. -/
theorem tariff (P:Teller G) (L:Side) {W:ℝ} (o:Target.Order G W) (power:ℝ) :
    ∃E,Rate G L power E ∧ ∀ᶠx:ℝ in atTop,0≤E x ∧
      ∀{c f:Side}{S:StepData c f}{T:Tube G S}{R:Rep G f}{Q:ConnectedActivityE6.Target G P}{μ C:ℝ}
        (_H:Cash W x μ L Q o C T R) {F:Forest S.ratio} (X:Coat T F), X.x=x→ X.width=o.K→ X.manifest→
        ∀Y:Support c,X.dice.real (eerie X Y o.ξ R.beta)≤Y.card*E x :=by
  obtain ⟨E,rate,paid⟩:=Coat.alarm_bills P L (η:=o.eta) (r:=o.gap) (Q:=o.ample) (Y:=o.indexPay) power o.rare
  refine ⟨E,rate,?_⟩
  filter_upwards [paid] with x bill
  refine ⟨bill.1,?_⟩
  intro c f S T R Q μ C H F X current fitted hg Y
  apply fracas
  intro i
  simpa only [card_singleton,pow_one] using
    bill.2 _ _ S T F X current H.laws.data.funds.length_eq (H.laws.data.localP F X current fitted hg).sails R
      (current.symm ▸ H.laws.intake) {i}

end YM.Integration.WilsonPositionSeparatedProfileMayerGateSafety
