import YM.Integration.WilsonPhysicalStationElectedEars
import YM.Integration.WilsonPhysicalStationBasisPosts
/-! The elected earlier fields and positive kinetic limit on the original two reporters. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationBasisOwners
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS Cells
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
open WilsonPhysicalStationSubtractedPair (lower)
open WilsonMovingForkReporterBothArms (Filed)
open PhysicalNext.Repeat Lotus MergeProof PhysicalNext.Repeat.Legato Bandage Campaign
open Next.Foundations Work.G08 Trace.Physical.GermGraph Next.Rank.Price
open WilsonPhysicalStationKineticLimit (transit)
open WilsonPhysicalStationRawReading (err)
open WilsonPhysicalStationSubtractedPosts (heard)
variable {G:Gauge}(R:Run G){T:Campaign R}(L:Pillars R T){f:Extraction.Order}{S:Table R.family.book}
  (fac:Facilities R.family f S)(F:Spec.Final R.family f S){ℓ:Ultrafilter (ℕ×ℕ)}
  (J₀:ℝ→tower S)(J:Scaling S)(V:∀i,Vane R.family i)
  {H:(Bel R.family.book).Hierarchy}{I:Type*}[Fintype I]{m k h e:ℕ}
local notation "rows" => R.family.labels.level h

open WilsonPhysicalStationElectedEars (Reads ready)
open WilsonPhysicalStationFullVote (Head)
open WilsonMovingForkReporterFixedRanks (Axes)
open WilsonPhysicalStationKineticLimit (coupling)
variable (hm:h  ≤  m)(hk:h  ≤  k)(ca:(V m).checked f H m)(cb:(V k).checked f H k)
local notation "idx" => Head R.family h
local notation "A₀" => V m
local notation "B₀" => V k
structure Earned (eh:e  ≤  h)(w:(idx)→(ℕ×ℕ)→R.family.label h)(v:(idx)→R.family.label h)(g:ℝ):Prop where
  chart (j:(idx))(p:ℕ×ℕ)(top:(B₀).k < p.1):if (B₀).k=(A₀).k then
    WilsonPhysicalStationCoincidentLower.Receipt R (A₀) (B₀) h e (Nat.lt_succ_of_le hm) (Nat.lt_succ_of_le hk)
      (p:=p.2) ca cb top j.val (w j p)
    else WilsonPhysicalStationSelectedLower.Receipt R (A₀) (B₀) h e (Nat.lt_succ_of_le hm) (Nat.lt_succ_of_le hk)
      (p:=p.2) ca cb top j.val (w j p)
  lower (j:(idx)):Tendsto (fun p:ℕ×ℕ=>(R.family.factory h p.1 p.2).terminal (w j p)) (ℓ:Filter _) (𝓝 (v j)) ∧
    S.project h (v j)∈LinearMap.range (F.sector.derivatives.rise eh)
  bracket:1/8  ≤  g ∧ g  ≤  12
  kinetic:Tendsto (transit R (A₀).k (B₀).k) (ℓ:Filter _) (𝓝 g)
  physical:Reads R (ℓ:=ℓ) J₀ J V hm hk w v

include L fac in
theorem original (simple:G.Simple)(below:(ℓ:Filter _)  ≤  f.fuse)
    {am bm ak bk:ℝ}(fine:Filed (f:=f) (l:=ℓ) J₀ J V h k ak bk)(coarse:Filed (f:=f) (l:=ℓ) J₀ J V h m am bm)
    (dates:(B₀).k=(A₀).k ∨ (B₀).k=(A₀).k+1)(horizon:h=e+1)(warm:WilsonPhysicalStationBasisClock.Live R (A₀).k)
    (rates:∀N p:ℕ,(A₀).k < N→1/8  ≤  transit R (A₀).k ((A₀).k+1) (N,p) ∧ transit R (A₀).k ((A₀).k+1) (N,p)  ≤  12):
    ∃ w v g,Earned R F (ℓ:=ℓ) J₀ J V hm hk ca cb (show e ≤ h by omega) w v g:=by
  rcases dates with same|next
  · obtain ⟨w,reg,v,landed,original⟩:=WilsonPhysicalStationElectedEars.coincident R fac F J₀ J V hm hk simple below
      fine coarse ca cb same horizon warm.old (by rw [same];exact warm.old) 
      (fun j:(idx)=>j.val) (fun j=>j.property)
    refine ⟨w,v,1,⟨?_,landed,by norm_num,?_,original⟩⟩
    · intro j p top
      simpa only [if_pos same] using reg j p top
    · apply tendsto_const_nhds.congr'
      filter_upwards [ready below (A₀).k] with p high
      let θ:=R.family.path.levels.clock.threshold (A₀).k
      have positive:0 < θ:=(R.family.path.levels.budget (A₀).k).threshold_pos
      have paid:shrink R.family (A₀).k p.1 p.2*θ=coupling R p.1 p.2 (A₀).k:=div_mul_cancel₀ _ positive.ne'
      have nonzero:0 < coupling R p.1 p.2 (A₀).k:=paid.symm.trans_gt (mul_pos (shrink_pos R.family R.makes high.le p.2) positive)
      simp only [transit,same,div_self nonzero.ne']
  · obtain ⟨w,reg,g,lo,hi,kin,v,landed,original⟩:=WilsonPhysicalStationElectedEars.adjacent R L fac F J₀ J V hm hk simple below
      fine coarse ca cb next horizon warm.old (by rw [next];exact warm.fine)
      (fun j:(idx)=>j.val) (fun j=>j.property) rates
    refine ⟨w,v,g,⟨?_,landed,⟨lo,hi⟩,kin,original⟩⟩
    intro j p top
    have diff:(B₀).k≠(A₀).k:=by omega
    simpa only [if_neg diff] using reg j p top

end YM.Integration.WilsonPhysicalStationBasisOwners
end
