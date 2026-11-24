import YM.Integration.WilsonRegisteredIntakeLeaves
import YM.Integration.WilsonRegisteredMarkedOffer

/-! The complete finite named collection of original measured old rows has its
own physically rooted and absolutely summable charge over each address.
Normalization of the original perturbative coupons is reversible even when a
row has zero cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredSectorSeats
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical


open WilsonCoherentMayerOldSlots AnalyticBridge.VerifiedReset

open PhysicalNext.Repeat.Legato WilsonInheritedRegisteredField
variable {G:Gauge} (R:Run G)




open MergeProof WilsonRegisteredMarkedOffer
variable {V:Type} [Fintype V] [DecidableEq V] {Γ:Marker.Census V}

def Filed {k N per:ℕ} (live:k≤N) (Q:Rep G (R.family.side k per)) (Γ:Marker.Census V):Prop:=
  ∀(d:V→ℕ)(_ref:∀a,R.family.ref (d a)≤k) (v:∀a,R.family.label (d a))
    (o:V→Site (R.family.side k per)),
  let P:=R.family.path.rep N per k
  let Y:=QLocalInheritedRegularSlots.carrier Q
  let Z:=fun a=>packet R.makes live (v a) (o a)
  let L:=fun a=>R.family.labels.level (d a)
  let cap:=fun a=>(R.family.path.levels.params k).columns*(L a).coeffSize ((L a).core (Z a).x)
  ∃e:V→ℕ→ℝ, (∀a,SumBudget (fun i=>P.p.mass ((Z a).support i) (e a i)) (cap a)) ∧
    (Q.p.supportExponent≤P.p.supportExponent →
      ∀a,SumBudget (fun i=>Q.p.mass ((Z a).support i) (e a i)) (cap a)) ∧
    ∀(i:V→ℕ)(χ:V→ℂ→L[ℝ]ℝ), (∀a z,|χ a z|≤‖z‖) →
    ∃b:V→Leaf Y,(∀a,(b a).weight=e a (i a) ∧ (b a).crest=(Z a).support (i a) ∧ o a∈(b a).crest) ∧
      (∀a U,(b a).ingredient U=χ a ((Z a).maskedTerm P (i a) U)) ∧
      ∀(s:V→Γ.Mode)(_single:∀a,(s a).val={a})(liveMode:∀a,(s a).val.Nonempty),
        let D:=1+(Fintype.card V:ℝ)*Fintype.card V
        let M:=fun a=>hat Y D (b a) (s a) (liveMode a)
        (∀a,(s a).val.image o⊆(b a).crest) ∧
        Menu.Offer o M (fun _=>1) Y.p.B Y.p.supportExponent (Fintype.card V*D⁻¹) ∧
        ∀a U,((D*mass Y (b a):ℝ):ℂ)*(M a).charge*((M a).M.ingredient U:ℂ)=
          (χ a ((Z a).maskedTerm P (i a) U):ℂ)

theorem original {k N per f t:ℕ} {s:ℝ} (live:k≤N)
    (onset:R.family.ref (max f t)≤k) (Q:Rep G (R.family.side k per))
    (record:LocalComparison.NormAt R.family k Q.p f t s):Filed R live Q Γ:=by
  intro d ref v o P Y Z L cap
  choose e bill reserve leaf using fun a=>WilsonRegisteredIntakeLeaves.issued R live (ref a) onset Q
    record (v a) (o a)
  refine ⟨e,bill,fun narrow a=>reserve a (record.reserve ▸ narrow),?_⟩
  intro i χ contract
  choose b price site contains read using fun a=>leaf a (i a) (χ a) (contract a)
  refine ⟨b,fun a=>⟨price a,site a,contains a⟩,read,?_⟩
  intro s single liveMode D M
  have roots a:(s a).val.image o ⊆ (b a).crest:=by
    rw [single a,Finset.image_singleton,Finset.singleton_subset_iff]
    exact contains a
  have pos:0<D:=by dsimp only [D];positivity
  refine ⟨roots,WilsonRegisteredMarkedOffer.offered Y pos o b s liveMode roots,?_⟩
  intro a U
  rw [←read a U]
  exact WilsonRegisteredMarkedOffer.original Y pos (b a) (s a) (liveMode a) U

end YM.Integration.WilsonRegisteredSectorSeats
