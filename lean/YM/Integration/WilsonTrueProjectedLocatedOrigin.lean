import YM.Integration.WilsonTrueProjectedLocatedBalance
import YM.Integration.WilsonOriginalNullOriginGrid
/-! On the aligned part of the original course every emitted primary and its
later feeds are pushes of one bare field. Their whole finite sum belongs to
the exact calibrated image at the landing, irrespective of its raw size. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedLocatedOrigin
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

def image {d N p b : ℕ} (o : ∀ i,Site ((C₀).side i p)) (room : Opened C₀ d b p)
    (live : b ≤ N) : (C₀).label d →+ (Config G ((C₀).side b p) → ℂ) where
  toFun := placed R d N p b o 0
  map_zero' := by
    funext U;exact congrFun (zero_cal (C:=R.family) d N p b R.makes room.post live) (Lattice.translate (o b) U)
  map_add' := by
    intro x y;funext U; exact congrFun (cal_add (C:=R.family) d N p b R.makes room.post live x y) (Lattice.translate (o b) U)

theorem original {d N p b n : ℕ} {W : ∀ j,Rep G ((C₀).side j p)}
    {o : ∀ j,Site ((C₀).side j p)} {F : ∀ j,Config G ((C₀).side (b+j) p) → ℂ}
    {price : ℕ → ℝ} {ε total : ℝ} (H : Receipt R d N p b n W o F price ε)
    (paid : (∑ j : Fin n,(H.u j+H.e j)) ≤ total) (live : b+n≤N)
    (room : Opened C₀ d b p) {σ C Λ δ w : ℝ} (law : (W b).Lawful σ C Λ δ w)
    (dw : d≤(W b).p.order) (pw : d≤(W b).p.power)
    (grid : ∀ i≤n,o (b+i)=((C₀).S.toDepth (show b≤b+i by omega) p).embed (o b))
    (v : (C₀).label d) (top : F n=placed R d N p b o n v) :
    let S:=(C₀).localSection d
    let L:=(C₀).labels.level d
    let P:=(C₀).path.rep N p b
    let x:=v-(∑j:Fin n,∑i∈Finset.range j.val,H.feed j i)-∑j:Fin n,H.primary j
    ∃ h q : store C₀ d p b,
      h.Format (o b) (C₀).params (W b) ∧ q.Format (o b) (C₀).params P ∧
      h.remBound (o b) (W b) (safety C₀ b) (∑ j,H.u j) ∧ q.remBound (o b) P (safety C₀ b) (∑ j,H.e j) ∧
      projection L (C₀).params (W b).p.threshold (o b) h=0 ∧ projection L (C₀).params P.p.threshold (o b) q=0 ∧
      L.coeffSize h.x ≤ tPrice L (C₀).params (W b)*(∑j,H.u j) ∧
      L.coeffSize q.x ≤ tPrice L (C₀).params P*(∑j,H.e j) ∧
      (∑j,H.u j)+(∑j,H.e j)≤total ∧
      placed R d N p b o 0 x=F 0+h.density (o b) S (W b)+q.density (o b) S P := by
  classical
  intro S L P x
  let J:=image R o room (show b≤N by omega)
  have fold (i:ℕ) (small:i≤n) (y:(C₀).label d):
      flow C₀ d N p b i (placed R d N p b o i y)=J y:=by
    change WilsonOriginalNullPlacedFlowPanel.field R d N p b i (o (b+i)) y=_
    rw [grid i small]
    exact WilsonOriginalNullOriginGrid.aligned R d N p room.post (o b) y i (by omega)
  obtain ⟨h,q,hf,qf,hp,qp,hz,qz,hr,qr,bill,field⟩:=
    WilsonTrueProjectedLocatedBalance.original R H paid (by omega) room law dw pw
  refine ⟨h,q,hf,qf,hp,qp,hz,qz,hr,qr,bill,?_⟩
  have feeds : (∑j:Fin n,∑i∈Finset.range j.val,flow C₀ d N p b i (placed R d N p b o i (H.feed j i)))=
      J (∑j:Fin n,∑i∈Finset.range j.val,H.feed j i) := by
    simp only [map_sum]
    apply Finset.sum_congr rfl;intro j _
    apply Finset.sum_congr rfl;intro i hi
    exact fold i ((Finset.mem_range.mp hi).le.trans j.isLt.le) (H.feed j i)
  have heads : (∑j:Fin n,flow C₀ d N p b j.val (placed R d N p b o j.val (H.primary j)))=
      J (∑j:Fin n,H.primary j) := by
    simp only [map_sum]
    exact Finset.sum_congr rfl (fun j _=>fold j.val j.isLt.le (H.primary j))
  rw [top,fold n le_rfl,feeds,heads] at field
  change J (v-_-_)=_
  rw [map_sub,map_sub,field]
  abel

end YM.Integration.WilsonTrueProjectedLocatedOrigin
