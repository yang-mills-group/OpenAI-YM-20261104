import YM.Integration.WilsonPositionSeparatedProfileMayerLeading
import YM.Integration.WilsonCoherentMayerOccurrences
import YM.Integration.WilsonCoherentMayerSubmission
import YM.LocalLTE.Fan.Buds

/-! The original zero-decoration term on actual submitted fields, with every
older marked partner and each original support and angular cutoff retained. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileMayerMasks
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
variable {run:Run G} {I:Type} [Fintype I] (entry:Submitted run R I)

def gates (i:I) (a:ℝ) (X:Coat T F) (z:momentSpace X):ℝ:=
  if Healthy R.p.threshold (R.activities.reg (entry.key i)).support (field R X z)
  then anchor R a (.logKey (entry.key i)) X z else 0

omit [Fintype I] in
theorem priced (i:I) (a:ℝ) (X:Coat T F) (z:momentSpace X) : gates entry i a X z∈Set.Icc 0 1:=by
  unfold gates
  split
  · exact (X.wrapY z.1).conserve _ _ _
  exact ⟨le_rfl,zero_le_one⟩

theorem products (old:Team R) (fresh:∀m∈old.own,∀i,m.turn≠(row entry i).turn)
    (X:Coat T F) (z:momentSpace X) :
    (∏h∈(together entry old fresh).signs S,(Laminate.partner (together entry old fresh) H h).joint X z)=
    (∏m∈old.own,m.ingredient (field R X z)*anchor R o.a m.turn X z)*
      (∏i,WilsonCoherentMayerEntry.raw run (entry.label i) (entry.site i) R.p.threshold (entry.phase i) (field R X z))*
      ∏i,gates entry i o.a X z :=by
  let prior:=together entry old fresh
  have unshared:Disjoint old.own (occupied entry):=by
    apply Finset.disjoint_left.mpr
    intro m live found
    obtain ⟨i,_,eq⟩:=Finset.mem_image.mp found
    exact fresh m live i (congrArg Leaf.turn eq.symm)
  change (∏h∈prior.signs S,(Laminate.partner prior H h).joint X z)=_
  rw [Team.signs,Finset.prod_image (Laminate.distinct prior S)]
  calc
    _=∏m∈prior.own,m.ingredient (field R X z)*anchor R o.a m.turn X z:=
      Finset.prod_congr rfl (fun m hm=>leaf (H:=H) prior m hm X z)
    _=_:=by
      change (∏m∈old.own∪occupied entry,m.ingredient (field R X z)*anchor R o.a m.turn X z)=_
      rw [Finset.prod_union unshared,occupied,Finset.prod_image (fun i _ j _ eq=>numbered entry eq),mul_assoc,←Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      change masked R.p.threshold (R.activities.reg (entry.key i)).support _ (field R X z)*_=_
      unfold gates
      split
      next he=> rw [masked_eq _ _ _ _ he];rfl
      next he=> rw [masked_ne _ _ _ _ he,zero_mul,mul_zero]

/-- With only the submitted fields, the original data land in the exact
family of Gaussian chambers used for the finite tagged sampler. -/
theorem chamber (old:Team R) (fresh:∀m∈old.own,∀i,m.turn≠(row entry i).turn) (empty:old.own=∅) :
    (together entry old fresh).signs S=LocalLTE.Fan.arm (univ.image (fun i:I=>(Sum.inl (entry.key i):LocalLTE.Fan.Veil c f))) :=by
  change (old.own∪univ.image (row entry)).image _=_
  rw [empty,Finset.empty_union,LocalLTE.Fan.arm,Finset.image_image,Finset.image_image]
  rfl

variable {η r q a Y D' A b v B C' ρ e uJ vJ θ K:ℝ}

theorem received (old:Team R) (fresh:∀m∈old.own,∀i,m.turn≠(row entry i).turn)
    (loc:H.ThinP) (minimal:loc.val=(together entry old fresh).signs S)
    (N:Captain H j C' D' Y B A b r a q n χ) (law:Awning H N.conduit A b ρ e uJ vJ k l)
    (room:Q.goal L s≤K) (allow:Mayer.Approved K θ j M) (inside:authorized H loc.val)
    (cohort:Mayer.Start loc.val) (V:Config G c) (healthy:Healthy (Pressure.temp s) (H.smallAt loc) V) :
    Laminate.column (together entry old fresh) loc.val H (χ:=χ) M (0:Orders M) V=
      likely fun i:Greenbelt.Reserve S=>likely fun tag:S.Choices=>
        let X:=((planted (prism T s χ o.K V (Greenbelt.allot i)) loc.val).taggedL tag)
        ∫z, (∏m∈old.own,m.ingredient (field R X z)*anchor R o.a m.turn X z)*
          (∏i,WilsonCoherentMayerEntry.raw run (entry.label i) (entry.site i) R.p.threshold (entry.phase i) (field R X z))*
          ∏i,gates entry i o.a X z ∂Insert.moment X :=by
  rw [WilsonPositionSeparatedProfileMayerLeading.measured _ loc minimal N law room allow inside cohort V healthy]
  congr 1; funext i; congr 1; funext tag
  apply integral_congr_ae
  filter_upwards with z
  rw [minimal]
  exact products entry old fresh _ _

end YM.Integration.WilsonPositionSeparatedProfileMayerMasks
