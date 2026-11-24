import YM.Integration.WilsonTrueProjectedLocatedPage
import YM.Integration.WilsonOriginalNullPlacedJointHistory
/-! A true rough null at the ultraviolet endpoint of an aligned interval.
Only its contracted represented remainder needs a small numerical norm. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedLocatedInitial
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


open WilsonTrueProjectedLocatedOrigin
variable {d N p b n : ℕ} {W : ∀ i,Rep G ((C₀).side i p)} {o : ∀ i,Site ((C₀).side i p)}
local notation "L" => (C₀).labels.level d
local notation "S" => (C₀).localSection d
local notation "P" => (C₀).path.rep N p
local notation "τ" => safety (C₀)

theorem aligned {o : ∀ i,Site ((C₀).side i p)} (live : b+n≤N) (home : Opened C₀ d b p)
    (grid : ∀ i≤n,o (b+i)=((C₀).S.toDepth (show b≤b+i by omega) p).embed (o b))
    (i : ℕ) (hi:i≤n) (x:(C₀).label d):
    flow C₀ d N p b i (placed R d N p b o i x) = image R o home (show b≤N by omega) x := by
  change WilsonOriginalNullPlacedFlowPanel.field R d N p b i (o (b+i)) x=_
  rw [grid i hi]
  exact WilsonOriginalNullOriginGrid.aligned R d N p home.post (o b) x i (by omega)

theorem original {W : ∀ i,Rep G ((C₀).side i p)} {o : ∀ i,Site ((C₀).side i p)} (live:b+n≤N) (home:Opened C₀ d b p)
    (grid : ∀ i≤n,o (b+i)=((C₀).S.toDepth (show b≤b+i by omega) p).embed (o b))
    (route : ∀ j<n,o (b+j)=((C₀).path.levels.clock.op (b+j) p).ratio.parent (o (b+j+1)))
    (laws : ∀ j<n,∃ a c f t s:ℝ,(W (b+j)).Lawful a c f t s)
    (houses : ∀ j<n,Opened C₀ d (b+j) p) {ε:ℝ} (ep:0≤ε)
    (gates : ∀ j<n,WilsonOriginalNullPlacedParallel.Joined C₀ d N p (b+j) W (o (b+j+1)) ε)
    (same : (W (b+n)).p=(P (b+n)).p) (quiet : ∀ U,(W (b+n)).eval U=(P (b+n)).eval U)
    (h k : store C₀ d p (b+n)) {B D:ℝ}
    (hf : h.Format (o (b+n)) (C₀).params (W (b+n))) (hp:h.remBound (o (b+n)) (W (b+n)) (τ (b+n)) B)
    (kf : k.Format (o (b+n)) (C₀).params (P (b+n))) (kp:k.remBound (o (b+n)) (P (b+n)) (τ (b+n)) D)
    (null : projection L (C₀).params (W (b+n)).p.threshold (o (b+n)) h+
      projection L (C₀).params (P (b+n)).p.threshold (o (b+n)) k=0) :
    ∃ (v w:store C₀ d p b) (x:(C₀).label d) (u e:ℝ),
      v.Format (o b) (C₀).params (W b) ∧ v.remBound (o b) (W b) (τ b) u ∧
      projection L (C₀).params (W b).p.threshold (o b) v=0 ∧
      w.Format (o b) (C₀).params (P b) ∧ w.remBound (o b) (P b) (τ b) e ∧
      projection L (C₀).params (P b).p.threshold (o b) w=0 ∧ u+e≤gain C₀ b (b+n)*(B+D) ∧
      flow C₀ d N p b n (h.density (o (b+n)) S (W (b+n))+k.density (o (b+n)) S (P (b+n)))=
        v.density (o b) S (W b)+w.density (o b) S (P b)+placed R d N p b o 0 x := by
  classical
  obtain ⟨v,w,x,u,e,vf,vp,vz,wf,wp,wz,paid,_,field⟩:=WilsonOriginalNullPlacedJointHistory.finite
    R d N p b W o ep n live route laws houses gates same quiet h k B D hf hp kf kp null
  refine ⟨v,w,∑ j∈Finset.range n,x j,u,e,vf,vp,vz,wf,wp,wz,paid,?_⟩
  let J:=image R o home (show b≤N by omega)
  have sum : (∑j∈Finset.range n,flow C₀ d N p b j (placed R d N p b o j (x j)))=J (∑j∈Finset.range n,x j):=by
    rw [map_sum]; exact Finset.sum_congr rfl (fun j hj=>aligned R live home grid j (Finset.mem_range.mp hj).le (x j))
  exact field.trans (congrArg (fun f=>v.density (o b) S (W b)+w.density (o b) S (P b)+f) sum)

end YM.Integration.WilsonTrueProjectedLocatedInitial
