import YM.Integration.WilsonPhysicalStationGradedHearing
import YM.Integration.WilsonPhysicalStationObservedGrid

/-! Original regulator limit of the signed corrected top-rank vote on the elected two physical reporters. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationPureReceipt
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS Cells
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open Further.CorrectedLift Next.Rank Next.Rank.Station
open WilsonPhysicalStationFullVote (Head Below principal lowerRow)
open WilsonPhysicalStationElectedEars (Reads)
open WilsonPhysicalStationGradedVoter (portion)
open scoped Topology Classical BigOperators Matrix

variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}{H:(Bel R.family.book).Hierarchy}
    {ℓ:Ultrafilter (ℕ×ℕ)}(J₀:ℝ→tower S)(J:Scaling S)(V:∀i,Vane R.family i)
    {m k h:ℕ}(hm:h ≤ m)(hk:h ≤ k)(cb:(V k).checked f H k)(q:ℕ)

def ballot (u:(standard R.family).Field h):(standard R.family).Field h:=
  portion R.family h (·=(h,q)) ((J.U k h).symm (J₀ (V k).wheel.r h u))

def coefficients (u:(standard R.family).Field h)(i:Head R.family h):ℂ:=
  ladder R.family h (ballot R J₀ J V (k:=k) q u) i.val

theorem supported (u:(standard R.family).Field h)(i:Head R.family h):
    coefficients R J₀ J V (k:=k) q u i=if ((R.family.labels.level h).grades i.val).2=q then
      ladder R.family h ((J.U k h).symm (J₀ (V k).wheel.r h u)) i.val else 0:=by
  unfold coefficients ballot
  rw [WilsonPhysicalStationGradedVoter.tally]
  simp [Prod.ext_iff,i.property]

variable (w:Head R.family h→(ℕ×ℕ)→R.family.label h)(v:Head R.family h→R.family.label h)

def signed (u z:(standard R.family).Field h)(j:ℕ)(o:Fin 2 → Cover)(p:ℕ×ℕ):ℂ:=
  if top:(V k).k<p.1 then
    let peer:=(V m).wheel.atCut p ⟨h,Nat.lt_succ_of_le hm⟩ ((J.U m h).symm (J₀ (V m).wheel.r h z))
    ∑i:Head R.family h,coefficients R J₀ J V (k:=k) q u i*principal R (V k) (Nat.lt_succ_of_le hk) (per:=p.2) cb top w j o peer i
  else 0

def left (u:(standard R.family).Field h):S.Field h:=
  J.U k h (ballot R J₀ J V (k:=k) q u)-
    S.project h (∑i:Head R.family h,coefficients R J₀ J V (k:=k) q u i • v i)

theorem original (below:(ℓ:Filter _) ≤ f.fuse)(bought:Reads R (ℓ:=ℓ) J₀ J V hm hk w v)
    (u z:(standard R.family).Field h)(j:ℕ)(o:Fin 2 → Cover)(safe:Extraction.Order.grid R.family j o∈conf 2):
    Tendsto (signed R J₀ J V hm hk cb q w u z j o) (ℓ:Filter _)
      (𝓝 (S.classMoment S (fun _:Fin 2=>h) (Extraction.Order.grid R.family j o)
        ![left R J₀ J V (k:=k) q v u,J₀ (V m).wheel.r h z])):=by
  let y:=ballot R J₀ J V (k:=k) q u
  let c:=coefficients R J₀ J V (k:=k) q u
  have ready:=bought c ((J₀ (V k).wheel.r h).symm (J.U k h y)) z j o safe
  simp only [LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply] at ready
  apply ready.congr'
  filter_upwards [WilsonPhysicalStationElectedEars.ready below (V k).k] with p top
  let peer:=(V m).wheel.atCut p ⟨h,Nat.lt_succ_of_le hm⟩ ((J.U m h).symm (J₀ (V m).wheel.r h z))
  have paid:=WilsonPhysicalStationFullVote.original R (V k) (Nat.lt_succ_of_le hk) (per:=p.2) cb top y w j o peer
  dsimp only at paid
  have vanishes:(∑i:Below R.family h,ladder R.family h y i.val*
      lowerRow R (V k) (Nat.lt_succ_of_le hk) (per:=p.2) cb top j o peer i)=0:=by
    apply Finset.sum_eq_zero
    intro i _
    have off:¬(R.family.labels.level h).grades i.val=(h,q):=fun eq=>i.property (congrArg Prod.fst eq)
    have hz:ladder R.family h y i.val=0:=WilsonPhysicalStationGradedVoter.outside R.family h _ _ i.val off
    rw [hz,zero_mul]
  rw [vanishes,add_zero] at paid
  unfold signed
  rw [dif_pos top]
  exact paid

theorem tested (below:(ℓ:Filter _) ≤ f.fuse)(bought:Reads R (ℓ:=ℓ) J₀ J V hm hk w v)
    (u z:(standard R.family).Field h){I:Type*}[Fintype I](μ:I→ℂ)(ξ:I→Points 2)
    (fit:∀i,FitSky R.family.path.levels (V m).b (V m).k (ξ i)):
    Tendsto (fun p=>∑i,μ i*signed R J₀ J V hm hk cb q w u z (V m).k
      (choose R.family.path.levels (V m).b (V m).k (ξ i)) p) (ℓ:Filter _)
      (𝓝 (∑i,μ i*S.classMoment S (fun _:Fin 2=>h) ((V m).wheel.r • tested R.family.path.levels (V m).b (V m).k (ξ i))
        ![left R J₀ J V (k:=k) q v u,J₀ (V m).wheel.r h z])):=by
  apply tendsto_finsetSum _ fun i _=>tendsto_const_nhds.mul ?_
  rw [←WilsonPhysicalStationObservedGrid.actual R (V m) (ξ i)]
  exact original R J₀ J V hm hk cb q w v below bought u z _ _ (WilsonPhysicalStationObservedGrid.separated R (V m) (ξ i) (fit i))

end YM.Integration.WilsonPhysicalStationPureReceipt
end
