import YM.Integration.WilsonCoherentMayerOccurrences

/-! The quoted expense of the actual remaining signed Mayer cofactor once
the submitted ordinary marks have been separated at their original addresses. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerCofactor
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

theorem capital (prior:Team R) (chosen:Finset (Leaf R)) (enrolled:chosen⊆prior.own)
    (ordinary:∀m∈chosen,∃i,m.turn=.logKey i) :
    (team prior chosen).weight=∏m∈prior.own\chosen,m.weight :=by
  have distinct:Set.InjOn (place chosen) (prior.own:Set (Leaf R)):=by
    intro x hx y hy h
    exact prior.alone hx hy (by simpa [WilsonCoherentMayerGate.address] using congrArg Leaf.turn h)
  unfold Team.weight team
  rw [Finset.prod_image distinct,← Finset.prod_sdiff enrolled]
  have cut : (∏m∈chosen,(place chosen m).weight)=1 :=by
    apply Finset.prod_eq_one
    intro m hm
    obtain ⟨i,hi⟩:=ordinary m hm
    rw [WilsonCoherentMayerGate.place,if_pos hm]
    exact (regular hi 1).1
  rw [cut,mul_one]
  exact Finset.prod_congr rfl fun m hm=>by rw [WilsonCoherentMayerGate.place,if_neg (Finset.mem_sdiff.mp hm).2]

include law room allow
theorem funded (prior:Team R) (chosen:Finset (Leaf R)) (enrolled:chosen⊆prior.own)
    (ordinary:∀m∈chosen,∃i,m.turn=.logKey i) (raw:Leaf R → Config G f → ℝ)
    (reading:∀m∈chosen,∀U,m.turn.qualifies R U→m.ingredient U=raw m U)
    (before:prior.signs S⊆p) (u:Mayer.Decors (p\prior.signs S) M) (hw:Mayer.decorOrder u≤M)
    (cohort:Mayer.Start (p\prior.signs S)) (reserve:(M+4:ℝ)*r≤α) (charge:1≤α)
    (speed:ζ≤α) (inside:authorized H p)
    (X:Coat T F) (healthy:Healthy (Pressure.temp s) (H.unionP p) X.V)
    (hx:X.x=s) (hk:X.width=o.K) (hχ:X.χ=χ) (hm:X.manifest) (z:momentSpace X) :
    let kept:=team prior chosen
    let remainder:=Mayer.planned H p u (Laminate.partner kept H) X z
    Mayer.planned H p u (Laminate.partner prior H) X z=
      (∏m∈chosen,raw m (WilsonCoherentMayerOccurrences.field R X z))*remainder ∧
    |remainder|≤(X.catastrophe (o.ξ/2) R.beta (blaze p)).indicator
       (fun _=>(∏m∈prior.own\chosen,m.weight)*
         ∏i:↥(p\prior.signs S),θ*(N.conduit.tag i.val)^((u i).val+1)) z.2:=by
  dsimp only
  refine ⟨WilsonCoherentMayerOccurrences.original prior chosen enrolled ordinary raw reading before u X z,?_⟩
  let kept:=team prior chosen
  have bill : Mayer.tariff N.conduit p θ u (Laminate.coverWeight kept S)=
        (∏m∈prior.own\chosen,m.weight)*∏i:↥(p\prior.signs S),θ*(N.conduit.tag i.val)^((u i).val+1) :=by
    unfold Mayer.tariff
    apply congrArg (· * _)
    calc
      _ = ∏i∈kept.signs S,Laminate.coverWeight kept S i := Finset.prod_congr ((Laminate.compartments prior p before).trans (census prior chosen S).symm) (fun _ _=>rfl)
      _ = _ := (Laminate.coverTotal kept S).trans (capital prior chosen enrolled ordinary)
  rw [←bill]
  refine WilsonCoherentMayerTariff.priced N law room allow u Finset.sdiff_subset hw _ _ ?_
    cohort reserve charge inside.2 X healthy hx hk hχ hm z
  intro i hi
  rw [Laminate.compartments prior p before,←census prior chosen S] at hi
  obtain ⟨m,hl,rfl⟩:=Finset.mem_image.mp hi
  unfold Laminate.partner Laminate.coverWeight
  rw [Laminate.chosenAt kept S _ _ m hl,Laminate.chosenAt kept S _ _ m hl]
  exact (Laminate.afford law m).weaken le_rfl speed

end YM.Integration.WilsonCoherentMayerCofactor
