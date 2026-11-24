import YM.Integration.WilsonTrueProjectedLocatedOrigin
import YM.Integration.WilsonOriginalNullPlacedJointGerm
import YM.Integration.WilsonOriginalNullFactoryRoute
/-! The measured coordinate of an aligned, independently printed group word.
The two projected remainders retain the separate original hard portfolios. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedLocatedPage
open Filter MeasureTheory Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open QuadraticLocal QuadraticLocal.Advent AllOrder AllOrder.Floe AllOrder.Transit WheelP WilsonOriginalNullCorridor
open scoped Classical Topology BigOperators

open FormalBulk08 City Pose RemainderComparison ConnectedActivityE6
open WilsonTrueProjectedPointProgram WilsonTrueProjectedPointInverse
open WilsonTrueProjectedLocatedBasis WilsonTrueProjectedLocatedHistory
open WilsonPinnedWidthTransport WilsonTrueProjectedNaturalFee WilsonTrueProjectedCourse
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G)
local notation "C₀" => R.family


open WilsonTrueProjectedLocatedFunded WilsonTrueProjectedLocatedMerge


open Push.Local Extra.Histories.Relay
theorem read {d N p b : ℕ} (live : b ≤ N) (home : Opened C₀ d b p)
    (o : Site ((C₀).side b p)) (W : Rep G ((C₀).side b p))
    (same : W.p=((C₀).path.rep N p b).p) (quiet : ∀ U,W.eval U=((C₀).path.rep N p b).eval U)
    {σ C Λ δ w : ℝ} (law : W.Lawful σ C Λ δ w) (x : (C₀).label d)
    (y h q : store C₀ d p b) (a u e : ℝ) :
    let P:=(C₀).path.rep N p b
    let L:=(C₀).labels.level d
    let S:=(C₀).localSection d
    y.Format o (C₀).params W → y.remBound o W (safety C₀ b) a →
    h.Format o (C₀).params W → h.remBound o W (safety C₀ b) u →
    q.Format o (C₀).params P → q.remBound o P (safety C₀ b) e →
    projection L (C₀).params W.p.threshold o h=0 → projection L (C₀).params P.p.threshold o q=0 →
    calValues (C:=C₀) d N p b x ∘ Lattice.translate o=y.density o S W+h.density o S W+q.density o S P →
    fitting (C:=C₀) d N p b R.makes home live x=projection L (C₀).params W.p.threshold o y := by
  intro P L S yf yp hf hp qf qp hz qz field
  let origin:=((C₀).factory d N p).entries b x
  let move:=Tour.placard C₀ R.makes N p live o
  let z:=Drift.stamp o move origin
  obtain ⟨zf,zp,_,zfield⟩:=WilsonOriginalNullFactoryRoute.entrance R d live home o x
  have stock:projection L (C₀).params P.p.threshold o z=fitting (C:=C₀) d N p b R.makes home live x:=by
    have pos:=WilsonOriginalNullRelocation.page L (C₀).params P.p.threshold 0 o move origin
    rw [zero_add] at pos
    have native:P.p=(C₀).path.levels.budget b:=(R.makes.wilson.represents N p b live).vac
    exact pos.trans (by change projection L (C₀).params P.p.threshold 0 origin=_;rw [native];rfl)
  have two:=presentation yf yp hf hp
  have added: (beside y h).density o S W=y.density o S W+h.density o S W:=plus law yp hp S
  have all:z.density o S P=(beside y h).density o S W+q.density o S P:=zfield.trans (field.trans (by rw [added]))
  have joined:=WilsonOriginalNullPlacedJointGerm.original R.family d N p b R.makes live home o W same quiet
    z (beside y h) q zf zp two.1 two.2 qf qp (fun U=>congrFun all U)
  have dims:=dimensions d N p b R.makes home.post live
  have dw:d≤W.p.order:=same ▸ dims.1
  have pw:d≤W.p.power:=same ▸ dims.2
  have split:=add_projection d y h yf hf dw pw ⟨_,_,yp⟩ ⟨_,_,hp⟩
  rw [←stock]
  calc
    _ = _ := joined
    _ = _ := by rw [split,hz,qz,add_zero,add_zero]

end YM.Integration.WilsonTrueProjectedLocatedPage
