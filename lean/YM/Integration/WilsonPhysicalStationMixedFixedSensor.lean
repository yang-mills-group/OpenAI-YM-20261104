import YM.Integration.WilsonPhysicalStationMixedHomogeneousCash
import YM.Integration.WilsonPhysicalStationLowerReceiver
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedFixedSensor
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
open WilsonPhysicalStationMixedBilledPort (base)
open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationKineticLimit (transit)
open WilsonPhysicalStationThermalBasisOffice (rank)
open WilsonPhysicalStationMixedCommittedBallot (signed)
open WilsonPhysicalStationMixedBallotCash (weighted)
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}(J₀:ℝ→tower S)(J:Scaling S)
    (V:∀i,Vane R.family i){m k h:ℕ}(hk:h ≤ k)(cb:(V k).checked f H k)
    (q Q:ℕ)(w:Head R.family h→(ℕ×ℕ)→R.family.label h)(v:Head R.family h→R.family.label h)
    {I:Type*}[Fintype I](r:I→Fin (m+1))(z:(i:I)→(standard R.family).Field (r i))(η:I→ℂ)(x:I→Points 2)
set_option quotPrecheck false
local notation "C₀"=>standard R.family
local notation "A₀"=>V m
local notation "B₀"=>V k
local notation "aX"=>R.family.path.levels
local notation "θ"=>R.family.path.levels.clock.monitor (V m).k
local notation "dl"=>(⟨h,Nat.lt_succ_of_le hk⟩:Fin (k+1))
local notation "sites" i=>tested (aX) (A₀).b (A₀).k (x i)
local notation "pins" i=>choose (aX) (A₀).b (A₀).k (x i)

open WilsonPhysicalStationMixedPortVoter (filed Pure)
open WilsonPhysicalStationMixedPostedMarket (Paid)
open WilsonPhysicalStationMixedBallotCash (pair)

open WilsonPhysicalStationMixedHomogeneousCash (wallet earlier)
open WilsonPhysicalStationLowerReceiver (ear)

def tip (j i:I):ℂ:=if i=j then 1 else 0

theorem one (i:I)(a:I→ℂ):∑j,tip i j*a j=a i:=by
  simp [tip,ite_mul]

include F in
theorem original (ca:(A₀).checked f H m)(simple:G.Simple)(below:(ℓ:Filter _)≤f.fuse)
    {ak bk:ℝ}(fine:Filed (f:=f) (l:=ℓ) J₀ J V h k ak bk)
    (coarse:∀i,∃a b:ℝ,Filed (f:=f) (l:=ℓ) J₀ J V (r i) m a b)
    (limits:∀a,Tendsto (fun p:ℕ×ℕ=>(R.family.factory h p.1 p.2).terminal (w a p)) (ℓ:Filter _) (𝓝 (v a)))
    {g W:ℝ}(heat:Tendsto (transit R (A₀).k (B₀).k) (ℓ:Filter _) (𝓝 g))
    (i:I)(bought:Paid R V hk cb q Q w r z (tip i) x W)(fits:∀i,FitSky (aX) (A₀).b (A₀).k (x i))
    (u:(C₀).Field h)(pure:Pure R q u):
    ‖ear R (S:=S) ((A₀).wheel.r • sites i) (J.U m (r i) (z i)) (J.U k h u-earlier R (S:=S) v u)-
      ((((B₀).wheel.r/(A₀).wheel.r)^h*g^q:ℝ):ℂ)*pair (C₀) h (r i) (sites i) u (z i)‖*(θ)^Q≤
        wallet R u*W*(θ)^q:=by
  have bought:=WilsonPhysicalStationMixedHomogeneousCash.original R F J₀ J V hk cb q Q w v r z (tip i) x ca simple
    below fine coarse limits heat bought fits u pure
  rw [one,one] at bought
  rw [WilsonPhysicalStationLowerReceiver.evaluated]
  exact bought

end YM.Integration.WilsonPhysicalStationMixedFixedSensor
end
