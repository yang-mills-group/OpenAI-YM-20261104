import YM.Integration.WilsonPhysicalStationMixedCommittedLower
import YM.Integration.WilsonPhysicalStationPureReceipt
import YM.Integration.WilsonPhysicalStationMixedListener
import YM.Integration.WilsonPhysicalStationThermalStart

/-! The charged raw head sum is the original subtracted physical voter on the shared regulator filter. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedCommittedBallot
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS Cells
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open Next.Rank Next.Rank.Station Next.Rank.Perch Next.Rank.Price
open Further.CorrectedLift (ladder)
open WilsonMovingForkReporterBothArms (Filed)
open WilsonOriginalBlissMixedGram (grades)
open WilsonPhysicalStationMixedWickPair (cell)
open WilsonPhysicalStationMixedWickTest (reference)
open WilsonMeasuredPublicEntranceOrderedPins (physical)
open scoped Topology Classical BigOperators
open WilsonPhysicalStationSubtractedPair (lower)
open WilsonPhysicalStationFullVote (Head Below)
open WilsonPhysicalStationPureReceipt (coefficients ballot left)
open WilsonPhysicalStationMixedListener (port value actual)
open WilsonPhysicalStationThermalStart (entered)
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}(J₀:ℝ→tower S)(J:Scaling S)
    (V:∀i,Vane R.family i){m k h:ℕ}(hk:h ≤ k)(dr:Fin (m+1))(cb:(V k).checked f H k)
    (q:ℕ)(w:Head R.family h→(ℕ×ℕ)→R.family.label h)(v:Head R.family h→R.family.label h)
set_option quotPrecheck false
local notation "C₀"=>Cells.standard R.family
local notation "dl"=> (⟨h,Nat.lt_succ_of_le hk⟩:Fin (k+1))
local notation "row"=>R.family.labels.level h
local notation "ds"=>grades h dr

def signed (u:(C₀).Field h)(z:(C₀).Field dr)(j:ℕ)(o:Fin 2 → Cover)(p:ℕ×ℕ):ℂ:=
  if top:(V k).k<p.1 then
    ∑a:Head R.family h,coefficients R J₀ J V (k:=k) q u a*WilsonPhysicalStationMixedListener.value R p.1 p.2 j o
      (entered R (V k) (dl) (p:=p.2) cb top (Pi.single a.val 1)-(R.family.factory h p.1 p.2).terminal (w a p))
      ((V m).wheel.atCut p dr z)
  else 0

theorem source (u:(C₀).Field h)(p:ℕ×ℕ)(top:(V k).k<p.1):
    (V k).wheel.atCut p (dl) (ballot R J₀ J V (k:=k) q u)-lower R (coefficients R J₀ J V (k:=k) q u) w p=
    ∑a:Head R.family h,coefficients R J₀ J V (k:=k) q u a •
      (entered R (V k) (dl) (p:=p.2) cb top (Pi.single a.val 1)-(R.family.factory h p.1 p.2).terminal (w a p)):=by
  let x:=ballot R J₀ J V (k:=k) q u
  let μ:=ladder R.family h x
  have off:(∑i:Below R.family h,μ i.val • WilsonPhysicalStationThermalPair.raw R (V k) (dl) (p:=p.2) cb top (Pi.single i.val 1))=0:=by
    apply Finset.sum_eq_zero
    intro i _
    have out:¬(row).grades i.val=(h,q):=fun eq=>i.property (congrArg Prod.fst eq)
    have hz:μ i.val=0:=WilsonPhysicalStationGradedVoter.outside R.family h _ _ i.val out
    rw [hz,zero_smul]
  have paid:=WilsonPhysicalStationFullVote.source R (V k) (Nat.lt_succ_of_le hk) (per:=p.2) cb top μ w
  rw [off,add_zero] at paid
  rw [←WilsonPhysicalStationThermalPair.lifted R (V k) (dl) cb top]
  exact paid

theorem returned (u:(C₀).Field h)(z:(C₀).Field dr)(j:ℕ)(o:Fin 2 → Cover)(p:ℕ×ℕ)(top:(V k).k<p.1):
    WilsonPhysicalStationMixedCommittedLower.watch R V (dl) dr (coefficients R J₀ J V (k:=k) q u) w
      (ballot R J₀ J V (k:=k) q u) z j o p=signed R J₀ J V hk dr cb q w u z j o p:=by
  unfold signed
  rw [dif_pos top]
  change WilsonPhysicalStationMixedListener.value R p.1 p.2 j o _ ((V m).wheel.atCut p dr z)=_
  rw [←actual,source R J₀ J V hk cb q w u p top]
  simp only [map_sum,map_smul,smul_eq_mul,actual]

include F in
theorem original (ca:(V m).checked f H m)(simple:G.Simple)(below:(ℓ:Filter _) ≤ f.fuse)
    {ak bk am bm:ℝ}(fine:Filed (f:=f) (l:=ℓ) J₀ J V h k ak bk)(coarse:Filed (f:=f) (l:=ℓ) J₀ J V dr m am bm)
    (converges:∀a,Tendsto (fun p:ℕ×ℕ=>(R.family.factory h p.1 p.2).terminal (w a p)) (ℓ:Filter _) (𝓝 (v a)))
    (u:(C₀).Field h)(z:(C₀).Field dr)(j:ℕ)(o:Fin 2 → Cover)(safe:Extraction.Order.grid R.family j o∈conf 2):
    Tendsto (signed R J₀ J V hk dr cb q w u z j o) (ℓ:Filter _)
      (𝓝 (S.classMoment S ds (Extraction.Order.grid R.family j o) (Fin.cons (α:=fun i=>S.Field (ds i))
       (left R J₀ J V (k:=k) q v u) (fun _=>J.U m dr z)))):=by
  have move:=WilsonPhysicalStationMixedCommittedLower.released R F J₀ J V (dl) dr cb ca
    (coefficients R J₀ J V (k:=k) q u) w v fine coarse simple below converges
    (ballot R J₀ J V (k:=k) q u) z j o safe
  apply move.congr'
  filter_upwards [WilsonPhysicalStationElectedEars.ready below (V k).k] with p top
  exact returned R J₀ J V hk dr cb q w u z j o p top

end YM.Integration.WilsonPhysicalStationMixedCommittedBallot
end
