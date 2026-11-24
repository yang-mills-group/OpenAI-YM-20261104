import YM.Integration.WilsonOriginalNullPlacedFlowPanel
import YM.Integration.WilsonOriginalNullPlacedGermMap

/-! The physical primary matrix over a finite displaced itinerary is
measured after the full chronological Wilson push. Each intermediate
stable feed and every hard exit is consequently included. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedFullMatrix
open Function Filter Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open WilsonOriginalNullPlacedGermMap
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "S₀" => (C₀).localSection d

structure Heard (η:ℝ) (N p b n:ℕ) (live:b+n ≤ N) (home:Opened C₀ d b p)
    (y:∀ j,Site ((C₀).side j p)) (A:(C₀).label d →ₗ[ℂ] (C₀).label d) : Prop where
  intrinsic (x:(C₀).label d) (z:Coefficient (F₀) ((C₀).side b p)) :
    let P:=(C₀).path.rep N p b
    Printed C₀ d N p b (y b) z (WilsonOriginalNullPlacedFlowPanel.field R d N p b n (y (b+n)) x) →
      projection F₀ (C₀).params P.p.threshold (y b) z=fitting d N p b R.makes home (by omega) (A x)
  deposited (x:(C₀).label d) :
    let P:=(C₀).path.rep N p b
    let M:=2*stock C₀ (b+n)*mCost C₀ d N p (b+n) x
    let bill:=WilsonOriginalNullPlacedCollar.cost R d η b (b+n)*M
    ∃ v z:Coefficient (F₀) ((C₀).side b p),
      z.Format (y b) (C₀).params P ∧ z.remBound (y b) P (safety C₀ b) bill ∧
      v.Format (y b) (C₀).params P ∧ v.remBound (y b) P (safety C₀ b) ((1+4*stock C₀ b)*bill) ∧
      projection F₀ (C₀).params P.p.threshold (y b) v=0 ∧ mCost C₀ d N p b (A x)≤2*bill ∧
      WilsonOriginalNullPlacedFlowPanel.field R d N p b n (y (b+n)) x=z.density (y b) S₀ P ∧
      z.density (y b) S₀ P=v.density (y b) S₀ P+(calValues (C:=C₀) d N p b (A x) ∘ Lattice.translate (y b))

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) {η:ℝ} (η0:0<η) :
    ∃ u:ℕ, ∀ b≥u, ∀ N p n, ∀ live:b+n ≤ N, ∀ y:∀ j,Site ((C₀).side j p),
      (∀ j<n,((C₀).path.levels.clock.op (b+j) p).ratio.parent (y (b+j+1))=y (b+j)) →
      ∃ (home:Opened C₀ d b p) (A:(C₀).label d →ₗ[ℂ] (C₀).label d), Heard R d η N p b n live home y A := by
  obtain ⟨v,paid⟩:=WilsonOriginalNullFactoryRoute.original R d simple shop η0
  obtain ⟨s,openAt⟩:=eventually_atTop.mp (open_late C₀ simple d)
  refine ⟨max v s,?_⟩;intro b later N p n live y route
  have hb:v ≤ b:=(le_max_left ..).trans later
  let home:Opened C₀ d b p:=openAt b ((le_max_right ..).trans later) p
  let high:Opened C₀ d (b+n) p:=openAt (b+n) (by omega) p
  let field:=WilsonOriginalNullPlacedFlowPanel.panel R d N p b n live high (y (b+n))
  have words (x:(C₀).label d):∃ z,Printed C₀ d N p b (y b) z (field x):=by
    obtain ⟨_,z,v,a,zf,zp,_,_,_,_,_,pair,_⟩:=paid b hb N p n live y route x
    exact ⟨z,zf,⟨_,zp⟩,pair.symm⟩
  obtain ⟨M,measured⟩:=WilsonOriginalNullPlacedGermMap.linear C₀ d N p b (y b) R.makes home
    (show b ≤ N by omega) field words
  let φ:=fitting d N p b R.makes home (show b ≤ N by omega)
  let A:=φ.symm.toLinearMap.comp M
  have chosen (x:(C₀).label d) (z:Coefficient (F₀) ((C₀).side b p)) (word:Printed C₀ d N p b (y b) z (field x)) :
      projection F₀ (C₀).params ((C₀).path.rep N p b).p.threshold (y b) z=φ (A x):=by
    change _=φ (φ.symm (M x));rw [φ.apply_symm_apply];exact (measured x z word).symm
  refine ⟨home,A,⟨chosen,?_⟩⟩;intro x lower mass bill
  obtain ⟨_,z,v,a,zf,zp,zg,vf,vp,vn,cost,whole,parts⟩:=paid b hb N p n live y route x
  have eq:A x=a:=φ.injective ((chosen x z ⟨zf,⟨_,zp⟩,whole.symm⟩).symm.trans zg)
  exact ⟨v,z,zf,zp,vf,vp,vn,eq ▸ cost,whole,eq ▸ parts⟩

theorem unique {η:ℝ} {N p b n:ℕ} {live:b+n ≤ N} {home:Opened C₀ d b p} {y:∀ j,Site ((C₀).side j p)}
    {A B:(C₀).label d →ₗ[ℂ] (C₀).label d}
    (first:Heard R d η N p b n live home y A) (other:Heard R d η N p b n live home y B) : A=B := by
  apply LinearMap.ext;intro x
  obtain ⟨v,z,zf,zp,_,_,_,_,field,_⟩:=first.deposited x
  have word:Printed C₀ d N p b (y b) z _:=⟨zf,⟨_,zp⟩,field.symm⟩
  exact (fitting d N p b R.makes home (by omega)).injective
    ((first.intrinsic x z word).symm.trans (other.intrinsic x z word))

end YM.Integration.WilsonOriginalNullPlacedFullMatrix
