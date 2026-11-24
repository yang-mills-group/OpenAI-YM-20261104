import YM.Integration.WilsonPhysicalStationMixedCommittedBallot
import YM.Integration.WilsonPhysicalStationMixedBallotCash
import YM.Integration.WilsonPhysicalStationMixedWithdrawnPort
/-! A financed mixed roster at the finite Wilson cutoff gives the same joint signed physical roster at the original ordered limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedPostedMarket
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

def observed {N per:ℕ}(top:(B₀).k<N)(a:Head R.family h)(i:I):ℂ:=
  WilsonPhysicalStationMixedListener.value R N per (A₀).k (pins i)
    (entered R (B₀) (dl) (p:=per) cb top (Pi.single a.val 1)-(R.family.factory h N per).terminal (w a (N,per)))
    ((A₀).wheel.atCut (N,per) (r i) (z i))

def born (a:Head R.family h)(i:I):ℂ:=base R h (z i) (sites i) a.val

def Paid (W:ℝ):Prop:=
  ∀ᶠ N:ℕ in atTop,∀per:ℕ,∀top:(B₀).k<N,∀a:Head R.family h,rank R.family h a.val=q→
    ‖(∑i,η i*observed R V hk cb w r z x (per:=per) top a i)-((signal R N per (A₀).k (B₀).k h q (mag (aX) (A₀).b (A₀).k) (mag (aX) (B₀).b (B₀).k):ℝ):ℂ)*∑i,η i*born R V r z x a i‖*(θ)^Q ≤ W*(θ)^q

private theorem exchange {A E:Type*}[Fintype A][Fintype E](α:A→ℂ)(β:E→ℂ)(y:A→E→ℂ):
    (∑i,α i*∑a,β a*y i a)=∑a,β a*∑i,α i*y i a:=by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  ring

def forecast (u:(C₀).Field h):ℂ:=
  ∑i,η i*WilsonPhysicalStationMixedBallotCash.pair (C₀) h (r i) (sites i) (ballot R J₀ J V (k:=k) q u) (z i)

def physicalRow (u:(C₀).Field h):ℂ:=
  ∑i,η i*WilsonPhysicalStationMixedBallotCash.pair S h (r i) ((A₀).wheel.r • sites i)
    (left R J₀ J V (k:=k) q v u) (J.U m (r i) (z i))

def signedRow (u:(C₀).Field h)(p:ℕ×ℕ):ℂ:=
  ∑i,η i*signed R J₀ J V hk (r i) cb q w u (z i) (A₀).k (pins i) p

theorem cash {W:ℝ}(bought:Paid R V hk cb q Q w r z η x W)(u:(C₀).Field h):
    ∀ᶠN:ℕ in atTop,∀per:ℕ,∀_top:(B₀).k<N,
    ‖signedRow R J₀ J V hk cb q w r z η x u (N,per)-((signal R N per (A₀).k (B₀).k h q (mag (aX) (A₀).b (A₀).k) (mag (aX) (B₀).b (B₀).k):ℝ):ℂ)*forecast R J₀ J V (k:=k) q r z η x u‖*(θ)^Q ≤
      (∑a:Head R.family h,‖coefficients R J₀ J V (k:=k) q u a‖)*W*(θ)^q:=by
  filter_upwards [bought] with N receipt
  intro per top
  let μ:=coefficients R J₀ J V (k:=k) q u
  let out:=observed R V hk cb w r z x (per:=per) top
  let ref:=born R V r z x (h:=h)
  have upper:signedRow R J₀ J V hk cb q w r z η x u (N,per)=∑a,μ a*∑i,η i*out a i:=by
    unfold signedRow signed
    simp only [dif_pos top]
    exact exchange η μ (fun i a=>out a i)
  have expected:forecast R J₀ J V (k:=k) q r z η x u=∑a,μ a*∑i,η i*ref a i:=by
    unfold forecast
    simp_rw [←WilsonPhysicalStationMixedBallotCash.free R J₀ J V (k:=k) q u]
    exact exchange η μ (fun i a=>ref a i)
  rw [upper,expected]
  apply weighted μ _ _ _ _ _ _ (pow_nonneg (Real.exp_pos _).le _)
  intro a nz
  apply receipt per top a
  by_contra bad
  apply nz
  exact (WilsonPhysicalStationPureReceipt.supported R J₀ J V (k:=k) q u a).trans (if_neg bad)

include F in
theorem released (ca:(A₀).checked f H m)(simple:G.Simple)(below:(ℓ:Filter _) ≤ f.fuse)
    {ak bk:ℝ}(fine:Filed (f:=f) (l:=ℓ) J₀ J V h k ak bk)
    (coarse:∀i,∃a b:ℝ,Filed (f:=f) (l:=ℓ) J₀ J V (r i) m a b)
    (limits:∀a,Tendsto (fun p:ℕ×ℕ=>(R.family.factory h p.1 p.2).terminal (w a p)) (ℓ:Filter _) (𝓝 (v a)))
    (fits:∀i,FitSky (aX) (A₀).b (A₀).k (x i))(u:(C₀).Field h):
    Tendsto (signedRow R J₀ J V hk cb q w r z η x u) (ℓ:Filter _)
      (𝓝 (physicalRow R J₀ J V (k:=k) q v r z η x u)):=by
  apply tendsto_finsetSum _ fun i _=>tendsto_const_nhds.mul ?_
  obtain ⟨a,b,held⟩:=coarse i
  have moved:=WilsonPhysicalStationMixedCommittedBallot.original R F J₀ J V hk (r i) cb q w v ca simple below
    fine held limits u (z i) (A₀).k (pins i) (WilsonPhysicalStationObservedGrid.separated R (A₀) _ (fits i))
  rw [WilsonPhysicalStationObservedGrid.actual] at moved
  exact moved

include F in
theorem original (ca:(A₀).checked f H m)(simple:G.Simple)(below:(ℓ:Filter _) ≤ f.fuse)
    {ak bk:ℝ}(fine:Filed (f:=f) (l:=ℓ) J₀ J V h k ak bk)
    (coarse:∀i,∃a b:ℝ,Filed (f:=f) (l:=ℓ) J₀ J V (r i) m a b)
    (limits:∀a,Tendsto (fun p:ℕ×ℕ=>(R.family.factory h p.1 p.2).terminal (w a p)) (ℓ:Filter _) (𝓝 (v a)))
    {g W:ℝ}(heat:Tendsto (transit R (A₀).k (B₀).k) (ℓ:Filter _) (𝓝 g))
    (bought:Paid R V hk cb q Q w r z η x W)(fits:∀i,FitSky (aX) (A₀).b (A₀).k (x i))
    (u:(C₀).Field h):
    ‖physicalRow R J₀ J V (k:=k) q v r z η x u-
      ((((B₀).wheel.r/(A₀).wheel.r)^h*g^q:ℝ):ℂ)*forecast R J₀ J V (k:=k) q r z η x u‖*(θ)^Q ≤
      (∑a:Head R.family h,‖coefficients R J₀ J V (k:=k) q u a‖)*W*(θ)^q:=by
  have phys:=released R F J₀ J V hk cb q w v r z η x ca simple below fine coarse limits fits u
  have warm:=WilsonPhysicalStationPureBorn.thermal R V (m:=m) (k:=k) (h:=h) q heat
  have hot:=Complex.continuous_ofReal.continuousAt.tendsto.comp warm
  obtain ⟨N₀,start⟩:=eventually_atTop.mp (cash R J₀ J V hk cb q Q w r z η x bought u)
  apply le_of_tendsto (((phys.sub (hot.mul_const _)).norm).mul_const _)
  filter_upwards [WilsonPhysicalStationElectedEars.ready (ℓ:=ℓ) below N₀,
    WilsonPhysicalStationElectedEars.ready (ℓ:=ℓ) below (B₀).k] with p large top
  exact start p.1 large.le p.2 top

end YM.Integration.WilsonPhysicalStationMixedPostedMarket
end
