import YM.Integration.WilsonCoherentMayerBorn
import YM.Integration.WilsonCoherentMayerSignedCharge

/-! The quoted expense of the actual remaining signed Mayer cofactor once
the submitted ordinary marks have been separated at their original addresses. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerDecorated
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
variable {G:Gauge} (run:Run G) {I:Type} [Fintype I] (d:I→ℕ)

def At (P:Teller G) (L:Side) (D:Patch) (taylor:ℕ) (s Ctable:ℝ):Prop:=
  ∀{c f:Side}{S:StepData c f}{T:Tube G S}{F:Forest S.ratio}{R:Rep G f}
    {Q:ConnectedActivityE6.Target G P}{W μ C:ℝ}{o:Target.Order G W}
    (H:Cash W s μ L Q o C T R) {j n l k M:ℕ} {χ:Chi}
    {q r a b Y D' v C' A B cost K θ δ ζ α:ℝ} {p:Molecule S}
    (N:Captain H j C' D' v Y A b r B q n χ)
    (_law:Awning H N.conduit A b cost a δ ζ k l) (_room:Q.goal L s≤K) (_allow:Mayer.Approved K θ j M)
    (entry:Submitted run R I) (_same:d=entry.grade) (_phase:∀i h,|entry.phase i h|≤‖h‖)
    (old:Team R) (fresh:∀m∈old.own,∀i,m.turn≠(row entry i).turn)
    (_before:(together entry old fresh).signs S⊆p)
    (u:Mayer.Decors (p\(together entry old fresh).signs S) M) (_hw:Mayer.decorOrder u≤M)
    (_cohort:Mayer.Start (p\(together entry old fresh).signs S)) (_reserve:(M+4:ℝ)*r≤α) (_charge:1≤α)
    (_speed:ζ≤α) (_inside:authorized H p)
    (X:Coat T F) (_healthy:Healthy (Pressure.temp s) (H.unionP p) X.V)
    (_hx:X.x=s) (_hk:X.width=o.K) (_hχ:X.χ=χ) (_hm:X.manifest) (_hot:0<R.beta)
    (_patch:S.patch=D) (_fixed:X.V=1) (_clear:Assembly.Clear S X.x X.seeds F),
    let prior:=together entry old fresh
    let kept:=team prior (occupied entry)
    let g:=Coat.gStep R.beta
    let costOld:=old.weight*∏i:↥(p\prior.signs S),θ*(N.conduit.tag i.val)^((u i).val+1)
    let integrand:=fun z:momentSpace X=>
       Mayer.planned H p u (Laminate.partner prior H) X z-
       Mayer.planned H p u (Laminate.partner kept H) X z*
         polynomial run entry.grade (F:=F) entry.site entry.phase R.p.threshold g entry.label taylor z.2
    Integrable integrand (moment X) ∧ (∫z,|integrand z| ∂moment X)≤costOld*
      (WilsonCoherentReportingPivot.mass run entry.grade R.p.threshold entry.label*(Ctable*g^(taylor+1)))

theorem purchased (P:Teller G) (L:Side) (D:Patch) (hd:D.Branches P.bind G) (taylor:ℕ):
    ∃Ctable:ℝ,0≤Ctable ∧ ∀ᶠ s:ℝ in atTop,At run d P L D taylor s Ctable:=by
  obtain ⟨Ctable,hc,all⟩:=WilsonCoherentMayerSignedCharge.original run d P L D hd taylor
  refine ⟨Ctable,hc,?_⟩
  filter_upwards [all] with s funded
  intro c f S T F R Q W μ C o H j n l k M χ q r a b Y D' v C' A B cost K θ δ ζ α p N law room allow
    entry same phase old fresh before u hw cohort reserve charge speed inside X healthy hx hk hχ hm hot patch fixed clear
  let prior:=together entry old fresh
  let rem:=Mayer.planned H p u (Laminate.partner (team prior (occupied entry)) H) X
  let w:=old.weight*∏i:↥(p\prior.signs S),θ*(N.conduit.tag i.val)^((u i).val+1)
  let g:=Coat.gStep R.beta
  have gw : 0<g:=inv_pos.mpr (Real.sqrt_pos.mpr hot)
  have hwgt:0≤w:=mul_nonneg (Finset.prod_nonneg fun m _=>m.profit)
    (Finset.prod_nonneg fun i _=>mul_nonneg (zero_le_one.trans allow.nonneg) (pow_nonneg (N.conduit.tagged _) _))
  have sold:=WilsonCoherentMayerBorn.earned N law room allow entry old fresh before u hw cohort reserve charge
    speed inside X healthy hx hk hχ hm hot
  have universal (z:momentSpace X):|rem z|≤w:=by
    apply (sold.2 z).2.trans
    by_cases struck:z.2∈X.catastrophe (o.ξ/2) R.beta (blaze p)
    · rw [Set.indicator_of_mem struck]
    · rw [Set.indicator_of_notMem struck];exact hwgt
  rw [same] at funded
  have pay:=funded c f S T F X hx patch H.laws.data.funds.length_eq H.laws.data.room hm
    H.laws.data.funds.funds fixed clear entry.site entry.phase phase R.p.threshold R.beta g hot gw
    entry.label rem hwgt sold.1 universal
  conv => dsimp only
  have eq:(fun z:momentSpace X=>Mayer.planned H p u (Laminate.partner prior H) X z-rem z*
      polynomial run entry.grade (F:=F) entry.site entry.phase R.p.threshold g entry.label taylor z.2)=
    fun z=>rem z*residual run entry.grade entry.site X entry.phase R.p.threshold R.beta g entry.label taylor z:=by
    funext z
    rw [(sold.2 z).1]
    unfold WilsonCoherentMayerSignedCharge.residual
    ring
  change Integrable _ _ ∧ (∫z,|Mayer.planned H p u (Laminate.partner prior H) X z-rem z*
      polynomial run entry.grade (F:=F) entry.site entry.phase R.p.threshold g entry.label taylor z.2| ∂moment X)≤_
  constructor
  · exact eq.symm ▸ pay.1
  · exact (show _ = _ from integral_congr_ae (Filter.Eventually.of_forall
      (fun z=>congrArg abs (congrFun eq z)))).trans_le pay.2

end YM.Integration.WilsonCoherentMayerDecorated
