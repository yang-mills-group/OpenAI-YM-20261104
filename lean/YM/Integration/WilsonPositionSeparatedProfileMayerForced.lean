import YM.Integration.WilsonPositionSeparatedProfileMayerGateReturn
import YM.Extra.WILSON_STARTUP.Face

/-! A genuine old forced occurrence requires its own prescribed bad site.
Its complete signed contribution is charged to that fixed local warning. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileMayerForced
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

open WilsonCoherentMayerSubmission WilsonCoherentMayerOccurrences WilsonPositionSeparatedProfileMayerMasks
open WilsonPositionSeparatedProfileMayerGateReturn LocalTaylorR2.Exponent
open private layers from YM.Integration.WilsonPositionSeparatedProfileMayerGateReturn
open private watchAt from YM.Integration.WilsonPositionSeparatedProfileMayerGateSafety
open private shared_measure from YM.Integration.WilsonPhysicalHistoryRetainedThermal
variable {run:Run G} {I:Type} [Fintype I]

def origins (S:StepData c f) (v:Site f):Support c:=halo 3 {S.ratio.parent v}

theorem size (S:StepData c f) (v:Site f):(origins S v).card≤7^4:=by
  simpa only [origins,Finset.card_singleton,one_mul] using Lattice.Corona.halo_size {S.ratio.parent v} 3

theorem vacant (m:Leaf R) {k:ℕ} (kind:m.turn=Wing.gasKey k) (v:Site f)
    (selected:v∈(R.activities.forced k).inventory) (X:Coat T F) (H:Cash W X.x μ L Q o C T R)
    (fitted:X.width=o.K) (manifest:X.manifest) (flat:X.blank=X) (stamped:Stamp T)
    (y:F.Slice G) (z:Air f G) (quiet:z∉eerie X (origins S v) o.ξ R.beta) : m.ingredient (field R X (y,z))=0:=by
  by_contra live
  have allowed:=m.grant (field R X (y,z)) live
  rw [kind] at allowed
  have eligible:(R.activities.forced k).eligible R.p.threshold (field R X (y,z)):=allowed
  have intersect:v∈(R.activities.forced k).support ∩ RG.flags R.p.threshold (field R X (y,z)):=eligible.1.symm ▸ selected
  have flagged:=(Finset.mem_inter.mp intersect).2
  let U:=X.input (worldZ X R.beta z)
  have info:=H.laws.data
  have yfield:=WilsonPositionSeparatedProfileMayerFlat.fields (R:=R) info.funds.funds X flat y z o.a m.turn
  have base:=WilsonPositionSeparatedProfileMayerFlat.fields (R:=R) info.funds.funds X flat X.Y z o.a m.turn
  have actual:field R X (y,z)=U:=yfield.1.trans base.1.symm
  rw [actual] at flagged
  obtain ⟨p,touches,excess⟩:=(RG.flags_spec _ _ _).mp flagged
  have hx:S.ratio.parent p.1∈origins S v:=by
    apply halo_spec.mpr;refine ⟨_,Finset.mem_singleton_self _,?_⟩
    have near:=Work.E04.parent_separation S.ratio v p.1
    have fine:=WilsonStartup.visit_near p touches;omega
  have old:=X.blank_no (S.ratio.parent p.1) (30*X.B)
  rw [flat] at old
  have lower:=info.safety.2.2.2 F X rfl fitted manifest
  have paid:=(lower.2 stamped (S.ratio.parent p.1) old R.beta H.laws.intake.positive z (watchAt X _ o.ξ z quiet hx)).2.1 p rfl
  rw [shine X info.room manifest] at paid
  rw [H.laws.intake.received.temp] at excess
  change X.t<toll U p at excess;change toll U p<X.t/4 at paid
  linarith [info.room.fiery]

theorem original (entry:Submitted run R I) (old:Team R) (m:Leaf R) (filed:m∈old.own)
    {k:ℕ} (kind:m.turn=Wing.gasKey k) (v:Site f) (selected:v∈(R.activities.forced k).inventory)
    (X:Coat T F) (H:Cash W X.x μ L Q o C T R) (fitted:X.width=o.K) (manifest:X.manifest)
    (flat:X.blank=X) (stamped:Stamp T) :
    |∫z,source entry old o.a X z*(∏i,gates entry i o.a X z) ∂Insert.moment X|≤
      X.dice.real (eerie X (origins S v) o.ξ R.beta)*bank entry old:=by
  let D:=eerie X (origins S v) o.ξ R.beta
  let B:=bank entry old
  let g:=fun z:momentSpace X=>∏i,gates entry i o.a X z
  have hm:MeasurableSet D:=measurable_eerie ..
  have dom:Integrable (fun z:momentSpace X=>D.indicator (fun _=>B) z.2) (Insert.moment X):=by
    change Integrable ((Prod.snd ⁻¹' D).indicator (fun _ : momentSpace X => B)) _
    exact (integrable_const B).indicator (hm.preimage measurable_snd)
  rw [←Real.norm_eq_abs]
  calc _≤∫z:momentSpace X,D.indicator (fun _=>B) z.2 ∂Insert.moment X:=by
        apply norm_integral_le_of_norm_le dom;filter_upwards with z
        by_cases hit:z.2∈D
        · rw [Set.indicator_of_mem hit,norm_mul]
          have hg:=layers entry o.a X z
          have normg:‖g z‖≤1:=by rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤g z from hg.1)];exact hg.2
          exact (mul_le_mul_of_nonneg_left normg (norm_nonneg _)).trans ((mul_one _).le.trans (bound entry old o.a X z))
        · rw [Set.indicator_of_notMem hit]
          have hv:=vacant m kind v selected X H fitted manifest flat stamped z.1 z.2 hit
          have gone:(∏m∈old.own,m.ingredient (field R X z)*anchor R o.a m.turn X z)=0:=Finset.prod_eq_zero filed (by rw [hv,zero_mul])
          simp only [source,gone,zero_mul,norm_zero,le_refl]
       _=X.dice.real D*B:=shared_measure X D hm B

end YM.Integration.WilsonPositionSeparatedProfileMayerForced
