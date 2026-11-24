import YM.Integration.WilsonPhysicalStationFullVoteResponse
import YM.Integration.WilsonPhysicalStationThermalFiledPair

/-! Read the full original nominated response on the precise snapped positions of the true coarser station. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationObservedGrid
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS Cells
open Trace.Terrace Trace.Over FVA2 FVA2.Register Trace.Physical.GermGraph Further.CorrectedLift
open Labels Next.Rank Next.Rank.Station Next.Rank.East Next.Rank.Price MeasureTheory Trace MergeProof.East
open WilsonPhysicalStationFullVote (Head)
open WilsonPhysicalStationElectedEars (Reads)
open WilsonPhysicalStationFullVoteResponse (posted)
open scoped Topology Classical BigOperators Matrix
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}{H:(Bel R.family.book).Hierarchy}
    {ℓ:Ultrafilter (ℕ×ℕ)}(J₀:ℝ→tower S)(J:Scaling S)(V:∀i,Vane R.family i)
    {m k h:ℕ}(hm:h ≤ m)(hk:h ≤ k)(cb:(V k).checked f H k)
local notation "A₀" => R.family.path.levels

theorem actual {D n:ℕ}(A:Vane R.family D)(x:Points n):
    Extraction.Order.grid R.family A.k (choose A₀ A.b A.k x)=A.wheel.r • tested A₀ A.b A.k x:=
  Next.Rank.Station.anchored _ _ _ _

theorem separated {D n:ℕ}(A:Vane R.family D)(x:Points n)(fits:FitSky A₀ A.b A.k x):
    Extraction.Order.grid R.family A.k (choose A₀ A.b A.k x)∈conf n:=by
  have paid:=Next.Rank.Ship.fittingSky fits
  intro i j same
  apply paid
  change (gap A₀ A.b A.k)⁻¹ • (Extraction.Order.grid R.family A.k (choose A₀ A.b A.k x) i)=
    (gap A₀ A.b A.k)⁻¹ • (Extraction.Order.grid R.family A.k (choose A₀ A.b A.k x) j)
  exact congrArg (fun y:E4=>(gap A₀ A.b A.k)⁻¹ • y) same

theorem original (below:(ℓ:Filter _) ≤ f.fuse)
    (w:Head R.family h→(ℕ×ℕ)→R.family.label h)(v:Head R.family h→R.family.label h)
    (bought:Reads R (ℓ:=ℓ) J₀ J V hm hk w v)(u z:(Bel R.family.book).Field h)
    {I:Type*}[Fintype I](μ:I→ℂ)(ξ:I→Points 2)(fit:∀i,FitSky A₀ (V m).b (V m).k (ξ i)):
    let A:=V m
    let a:=ladder R.family h ((J.U k h).symm (J₀ (V k).wheel.r h u))
    Tendsto (fun p=>∑i,μ i*posted R J₀ J V hm hk cb w u z A.k (choose A₀ A.b A.k (ξ i)) p) (ℓ:Filter _)
      (𝓝 (∑i,μ i*S.classMoment S (fun _:Fin 2=>h) (A.wheel.r • tested A₀ A.b A.k (ξ i))
        ![J₀ (V k).wheel.r h u-S.project h (∑b:Head R.family h,a b.val • v b),J₀ A.wheel.r h z])):=by
  intro A a
  have paid:=WilsonPhysicalStationFullVoteResponse.tested R J₀ J V hm hk cb below w v bought u z μ
    (fun _=>A.k) (fun i=>choose A₀ A.b A.k (ξ i)) (fun i=>separated R A (ξ i) (fit i))
  simpa only [actual R A] using paid

end YM.Integration.WilsonPhysicalStationObservedGrid
end
