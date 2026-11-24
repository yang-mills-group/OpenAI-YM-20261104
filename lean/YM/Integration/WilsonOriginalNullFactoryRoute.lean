import YM.Integration.WilsonOriginalNullPlacedCollar
import YM.Integration.WilsonOriginalNullPlacedFactory

/-! The original P factory receipt along a genuine displaced itinerary,
with the complete fitted coordinate remeasured once at the lower end. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullFactoryRoute
open Function Filter Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open WilsonOriginalNullCorridor
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" => R.family
local notation "S₀" => (C₀).localSection d
local notation "F₀" => (C₀).labels.level d

theorem entrance {N p t:ℕ} (live:t ≤ N) (home:Opened C₀ d t p) (y:Site ((C₀).side t p)) (x:(C₀).label d) :
    let P:=(C₀).path.rep N p t
    let q:=Drift.stamp y (Tour.placard C₀ R.makes N p live y) (((C₀).factory d N p).entries t x)
    let M:=2*stock C₀ t*mCost C₀ d N p t x
    q.Format y (C₀).params P ∧ q.remBound y P (safety C₀ t) M ∧ (F₀).coeffSize q.x ≤ M ∧
      q.density y S₀ P=calValues (C:=C₀) d N p t x ∘ Lattice.translate y := by
  intro P q M
  let h:=((C₀).factory d N p).entries t x
  let μ:=mCost C₀ d N p t x
  let φ:=fitting d N p t R.makes home live
  have loan:reads (C:=C₀) d N p t h M:=by
    have cert:=graph_cost d N p t R.makes home live x
    rw [fitting_apply] at cert;exact cert
  have shadow:(F₀).coeffSize q.x ≤ 2*μ:=(size_gap d N p t R.makes home live x).2
  have cap:2*μ ≤ M:=by
    change 2*μ ≤ (2*stock C₀ t)*μ
    exact mul_le_mul_of_nonneg_right (by linarith only [(stage C₀ t).columns_ge]) (Work.G08.size_nonneg (F₀) _)
  have facts:=WilsonOriginalNullRelocation.registered C₀ R.makes d N p t live 0 y h
  rw [zero_add] at facts
  refine ⟨?_,?_,shadow.trans cap,facts⟩
  · simpa only [zero_add] using Drift.stamp_format y (Tour.placard C₀ R.makes N p live y) h loan.1
  · have f:=Drift.stamp_rem y (Tour.placard C₀ R.makes N p live y) h loan.2
    rw [zero_add] at f;exact f

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) {η:ℝ} (η0:0<η) :
    ∃ onset:ℕ, ∀ b≥onset, ∀ N p (n:ℕ), ∀ late:b+n ≤ N, ∀ (y:∀ j,Site ((C₀).side j p)),
      (∀ j<n, ((C₀).path.levels.clock.op (b+j) p).ratio.parent (y (b+j+1))=y (b+j)) →
      ∀ (x:(C₀).label d),
      let lower:=(C₀).path.rep N p b
      let M:=2*stock C₀ (b+n)*mCost C₀ d N p (b+n) x
      let bill:=WilsonOriginalNullPlacedCollar.cost R d η b (b+n)*M
      ∃ (home:Opened C₀ d b p) (z v:Coefficient F₀ ((C₀).side b p)) (a:(C₀).label d),
        z.Format (y b) (C₀).params lower ∧ z.remBound (y b) lower (safety C₀ b) bill ∧
        projection F₀ (C₀).params lower.p.threshold (y b) z=fitting d N p b R.makes home (by omega) a ∧
        v.Format (y b) (C₀).params lower ∧ v.remBound (y b) lower (safety C₀ b) ((1+4*stock C₀ b)*bill) ∧
        projection F₀ (C₀).params lower.p.threshold (y b) v=0 ∧ mCost C₀ d N p b a ≤ 2*bill ∧
        flow C₀ d N p b n ((calValues (C:=C₀) d N p (b+n) x) ∘ Lattice.translate (y (b+n)))=z.density (y b) S₀ lower ∧
        z.density (y b) S₀ lower=v.density (y b) S₀ lower + (calValues (C:=C₀) d N p b a ∘ Lattice.translate (y b)) := by
  obtain ⟨u,walk⟩:=WilsonOriginalNullPlacedCollar.original R d simple shop η0
  obtain ⟨v,openAt⟩:=eventually_atTop.mp (open_late C₀ simple d)
  refine ⟨max u v,?_⟩
  intro b hb N p n late y route x lower M bill
  have home:Opened C₀ d b p:=openAt b ((le_max_right ..).trans hb) p
  have high:Opened C₀ d (b+n) p:=openAt (b+n) (by omega) p
  let q:=Drift.stamp (y (b+n)) (Tour.placard C₀ R.makes N p late (y (b+n))) (((C₀).factory d N p).entries (b+n) x)
  obtain ⟨qf,qp,qh,word⟩:=entrance R d late high (y (b+n)) x
  obtain ⟨z,zf,zp,zh,result⟩:=walk b ((le_max_left ..).trans hb) N p y n late route q M qf qp qh
  have here:b ≤ N:=by omega
  let α:=projection F₀ (C₀).params lower.p.threshold (y b) z
  let a:=(fitting d N p b R.makes home here).symm α
  obtain ⟨null,nf,np,nz,price,_,exactPair,filed⟩:=
    WilsonOriginalNullPlacedFiling.original C₀ R.makes d N p b home here (y b) z bill zf zp zh
  rw [filed] at exactPair
  refine ⟨home,z,null,a,zf,zp,((fitting d N p b R.makes home here).apply_symm_apply α).symm,nf,np,nz,price,?_,exactPair⟩
  exact (congrArg (flow C₀ d N p b n) word).symm.trans result

end YM.Integration.WilsonOriginalNullFactoryRoute
