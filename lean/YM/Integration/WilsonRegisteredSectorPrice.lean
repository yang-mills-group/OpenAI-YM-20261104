import YM.Integration.WilsonRegisteredMarkedOffer

/-! Every admitted occurrence can draw on the existing physical high-degree,
overlap and depth estimates. The original connected matrix and its
particular rooted reachability and directional fare are kept intact. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredSectorPrice
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy
open MergeProof LocalLTE
open scoped Topology BigOperators Classical


open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical


open WilsonInheritedRegisteredField RGLocalTaylor.Mayer PhysicalNext.Repeat.Daisy
open Push.AbsoluteSums ManuscriptQLocalMarkedHeightRun


variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V]
variable {c f L:Side} {S:StepData c f} {T:Tube G S} {Y:Rep G f}
  {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W b μ x:ℝ} {o:Target.Order G W}
  (E:Q.Expense) (H:Cash W x μ L Q o b T Y)

def Priced (J:Request V) (Γ:Marker.Census V) (price:ℝ) : Prop :=
  ∃A b C' d rv s z B e q:ℝ,∃k:ℕ,∃N:Captain H J.outputFieldOrder C' d rv s A b z B e k Chi.canonical,
    ManuscriptQLocalHeightPaidRows.Ready J.outputFieldOrder d B k ∧
    HostQ H N.conduit A B k ∧ Bikes Q L μ x E.earn q B J.outputFieldOrder k ∧
    (1≤betaF G x L ∧ Height.grow G L x^(length J)≤Real.exp (Q.mark L μ x) ∧
      Height.grow G L x^(length J)≤Real.exp (Q.ε*Pressure.Stores.till x) ∧
      ((betaF G x L)^2)^(Fintype.card V)*(Height.grow G L x^(length J))⁻¹≤price) ∧
    ∀(ι:Type)[Fintype ι] (leaf:ι→Leaf Y) (modes:ι→Γ.Mode)
      (occupied:∀i,(modes i).val.Nonempty) (origin:V→Site f),
      (∀i,(modes i).val.image origin⊆(leaf i).crest) →
      let D:=1+(Fintype.card V:ℝ)*Fintype.card ι
      let M:=fun i=>WilsonRegisteredMarkedOffer.hat Y D (leaf i) (modes i) (occupied i)
      let w:=fun _:V=>(1:ℝ)
    Ac.Hit (Captain.reachability (H:=H)) (radiusB x)
      (fun z=>Height.beaconN H (length J) z*Height.rocket H (fun _=>1) z*
        Height.markU N (fun i=>(M i).M) (fun i=>(betaF G x L)^(-(2:ℝ))*Menu.sumFee (M i) w)
          z J.outputDistanceOrder) E.earn 1 ∧
    Ac.Hit (fun z:Fan.Stars H (fun i=>(M i).M)=>Captain.reachability z.1) (radiusB x)
      (fun z=>if Height.tiredN H (length J) z.1 then
        Poly.price w (ManuscriptQLocalMarkedHeightTail.matrix H M z)*
          Captain.wife N z.1 (fun i=>(M i).M) z.2 J.outputDistanceOrder else 0) E.earn price


theorem paid (J:Request V) (Γ:Marker.Census V) (price:ℝ)
    (reserve:High E H J Γ price):Priced E H J Γ price:=by
  obtain ⟨a,b',C,d,rv,s,z,B,e,q,k,N,ready,host,bike,bands,debit⟩:=reserve
  refine ⟨a,b',C,d,rv,s,z,B,e,q,k,N,ready,host,bike,bands,?_⟩
  intro ι _ leaf modes occupied origin rooted D M w
  have D0:0<D:=by dsimp only [D];positivity
  have offer:=WilsonRegisteredMarkedOffer.offered Y D0 origin leaf modes occupied rooted
  have charge:(Fintype.card V:ℝ)*(Fintype.card ι*D⁻¹)≤1:=by
    rw [←mul_assoc,←div_eq_mul_inv]
    apply (div_le_one D0).2
    dsimp only [D];linarith
  exact debit ι M origin w (Fintype.card ι*D⁻¹) (fun _=>one_pos) offer (charge.trans bands.1)

end YM.Integration.WilsonRegisteredSectorPrice
