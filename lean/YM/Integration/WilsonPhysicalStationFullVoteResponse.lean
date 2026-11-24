import YM.Integration.WilsonPhysicalStationFullVote

/-! The signed full raw vote on the two appointed physical reporters converges through the original ordered cut. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationFullVoteResponse
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS Cells
open Trace.Terrace Trace.Over FVA2 FVA2.Register Trace.Physical.GermGraph Further.CorrectedLift
open Labels Next.Rank Next.Rank.East Next.Rank.Price MeasureTheory Trace MergeProof.East
open WilsonPhysicalStationFullVote (Head Below principal lowerRow)
open WilsonPhysicalStationElectedEars (Reads)
open WilsonPhysicalStationSubtractedPosts (heard)
open scoped Topology Classical BigOperators Matrix
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}{H:(Bel R.family.book).Hierarchy}
    {ℓ:Ultrafilter (ℕ×ℕ)}(J₀:ℝ→tower S)(J:Scaling S)(V:∀i,Vane R.family i)
    {m k h:ℕ}(hm:h ≤ m)(hk:h ≤ k)(cb:(V k).checked f H k)

def posted (w:Head R.family h→(ℕ×ℕ)→R.family.label h)(u z:(Bel R.family.book).Field h)
    (j:ℕ)(o:Fin 2 → Cover)(p:ℕ×ℕ):ℂ:=
  let x:=ladder R.family h ((J.U k h).symm (J₀ (V k).wheel.r h u))
  let peer:=(V m).wheel.atCut p ⟨h,Nat.lt_succ_of_le hm⟩ ((J.U m h).symm (J₀ (V m).wheel.r h z))
  if top:(V k).k < p.1 then
    (∑i:Head R.family h,x i.val*principal R (V k) (Nat.lt_succ_of_le hk) (per:=p.2) cb top w j o peer i)+
    ∑i:Below R.family h,x i.val*lowerRow R (V k) (Nat.lt_succ_of_le hk) (per:=p.2) cb top j o peer i
  else 0

theorem original (below:(ℓ:Filter _) ≤ f.fuse)
    (w:Head R.family h→(ℕ×ℕ)→R.family.label h)(v:Head R.family h→R.family.label h)
    (paid:Reads R (ℓ:=ℓ) J₀ J V hm hk w v)
    (u z:(Bel R.family.book).Field h)(j:ℕ)(o:Fin 2 → Cover)(safe:Extraction.Order.grid R.family j o∈conf 2):
    let x:=ladder R.family h ((J.U k h).symm (J₀ (V k).wheel.r h u))
    Tendsto (posted R J₀ J V hm hk cb w u z j o) (ℓ:Filter _)
      (𝓝 (S.classMoment S (fun _:Fin 2=>h) (Extraction.Order.grid R.family j o)
        ![J₀ (V k).wheel.r h u-S.project h (∑i:Head R.family h,x i.val • v i),J₀ (V m).wheel.r h z])):=by
  intro x
  apply (paid (fun i:Head R.family h=>x i.val) u z j o safe).congr'
  filter_upwards [WilsonPhysicalStationElectedEars.ready below (V k).k] with p top
  unfold posted
  rw [dif_pos top]
  exact WilsonPhysicalStationFullVote.original R (V k) (Nat.lt_succ_of_le hk) (per:=p.2) cb top
    ((J.U k h).symm (J₀ (V k).wheel.r h u)) w j o _

theorem tested (below:(ℓ:Filter _) ≤ f.fuse)
    (w:Head R.family h→(ℕ×ℕ)→R.family.label h)(v:Head R.family h→R.family.label h)
    (paid:Reads R (ℓ:=ℓ) J₀ J V hm hk w v)
    (u z:(Bel R.family.book).Field h){I:Type*}[Fintype I](μ:I→ℂ)(j:I→ℕ)(o:I→Fin 2 → Cover)
    (safe:∀i,Extraction.Order.grid R.family (j i) (o i)∈conf 2):
    let x:=ladder R.family h ((J.U k h).symm (J₀ (V k).wheel.r h u))
    Tendsto (fun p=>∑i,μ i*posted R J₀ J V hm hk cb w u z (j i) (o i) p) (ℓ:Filter _)
      (𝓝 (∑i,μ i*S.classMoment S (fun _:Fin 2=>h) (Extraction.Order.grid R.family (j i) (o i))
        ![J₀ (V k).wheel.r h u-S.project h (∑a:Head R.family h,x a.val • v a),J₀ (V m).wheel.r h z])):=by
  intro x
  exact tendsto_finsetSum _ fun i _=>tendsto_const_nhds.mul
    (original R J₀ J V hm hk cb below w v paid u z (j i) (o i) (safe i))

end YM.Integration.WilsonPhysicalStationFullVoteResponse
end
