import YM.Integration.WilsonOriginalNullPlacedGermMap
import YM.Integration.WilsonOriginalNullPlacedLinearPanel

/-! The same-operator measured primary map for a genuine Wilson factory
field at an arbitrary fine child and its true receiving parent. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedLinear
open Function Filter Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open WilsonOriginalNullPlacedLinearPanel WilsonOriginalNullPlacedGermMap
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "S₀" => (C₀).localSection d

structure Landed (N p i:ℕ) (live:i<N) (home:Opened C₀ d i p) (y:Site ((C₀).side (i+1) p))
    (A:(C₀).label d →ₗ[ℂ] (C₀).label d) : Prop where
  intrinsic (x:(C₀).label d) (z:Coefficient (F₀) ((C₀).side i p)) :
    let P:=(C₀).path.rep N p i
    let o:=((C₀).path.levels.clock.op i p).ratio.parent y
    Printed C₀ d N p i o z (held R d N p i y x) →
      projection F₀ (C₀).params P.p.threshold o z=fitting d N p i R.makes home live.le (A x)
  deposited (x:(C₀).label d) :
    let P:=(C₀).path.rep N p i
    let o:=((C₀).path.levels.clock.op i p).ratio.parent y
    let bill:=WilsonOriginalNullPlacedFactory.wage R d i*mCost C₀ d N p (i+1) x
    ∃ v z:Coefficient (F₀) ((C₀).side i p),
      z.Format o (C₀).params P ∧ z.remBound o P (safety C₀ i) bill ∧
      v.Format o (C₀).params P ∧ v.remBound o P (safety C₀ i) ((1+4*stock C₀ i)*bill) ∧
      projection F₀ (C₀).params P.p.threshold o v=0 ∧ mCost C₀ d N p i (A x)≤2*bill ∧
      held R d N p i y x=z.density o S₀ P ∧
      z.density o S₀ P=v.density o S₀ P+(calValues (C:=C₀) d N p i (A x) ∘ Lattice.translate o)

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) :
    ∀ᶠ i:ℕ in atTop, ∀ N p, ∀ live:i<N, Opened C₀ d (i+1) p → ∀ home:Opened C₀ d i p,
      ∀ y:Site ((C₀).side (i+1) p), ∃ A:(C₀).label d →ₗ[ℂ] (C₀).label d, Landed R d N p i live home y A := by
  filter_upwards [WilsonOriginalNullPlacedFactory.original R d simple shop] with i price
  intro N p live high home y
  let P:=(C₀).path.rep N p i
  let o:=((C₀).path.levels.clock.op i p).ratio.parent y
  let reader:=panel R d live high y
  have supply (x:(C₀).label d):∃ z,Printed C₀ d N p i o z (reader x):=by
    obtain ⟨z,v,a,zf,zp,_,_,_,_,_,field,_⟩:=price N p live high home y x
    exact ⟨z,zf,⟨_,zp⟩,field.symm⟩
  obtain ⟨M,measured⟩:=WilsonOriginalNullPlacedGermMap.linear C₀ d N p i o R.makes home live.le reader supply
  let φ:=fitting d N p i R.makes home live.le
  let A:=φ.symm.toLinearMap.comp M
  have chosen (x:(C₀).label d) (z:Coefficient (F₀) ((C₀).side i p)) (word:Printed C₀ d N p i o z (reader x)):
      projection F₀ (C₀).params P.p.threshold o z=φ (A x):=by
    change _=φ (φ.symm (M x))
    rw [φ.apply_symm_apply]
    exact (measured x z word).symm
  refine ⟨A,⟨chosen,?_⟩⟩
  intro x lower root bill
  obtain ⟨z,v,a,zf,zp,zg,vf,vp,vn,cost,field,full⟩:=price N p live high home y x
  have found:A x=a:=φ.injective ((chosen x z ⟨zf,⟨_,zp⟩,field.symm⟩).symm.trans zg)
  exact ⟨v,z,zf,zp,vf,vp,vn,found ▸ cost,field,found ▸ full⟩

theorem unique {N p i:ℕ} {live:i<N} {home:Opened C₀ d i p} {y:Site ((C₀).side (i+1) p)}
    {A B:(C₀).label d →ₗ[ℂ] (C₀).label d} (first:Landed R d N p i live home y A) (other:Landed R d N p i live home y B) : A=B := by
  apply LinearMap.ext;intro x
  obtain ⟨v,z,zf,zp,_,_,_,_,field,_⟩:=first.deposited x
  have word:Printed C₀ d N p i _ z (held R d N p i y x):=⟨zf,⟨_,zp⟩,field.symm⟩
  exact (fitting d N p i R.makes home live.le).injective ((first.intrinsic x z word).symm.trans (other.intrinsic x z word))

end YM.Integration.WilsonOriginalNullPlacedLinear
