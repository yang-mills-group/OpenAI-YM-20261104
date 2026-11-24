import YM.Integration.WilsonPhysicalChiralNonfreeStationMoney
import YM.Integration.WilsonMaxwellThermometerNominatedOrientation

/-! The complete rooted, signed maximal vote converges to the nominated
physical source, including when read through the finite-period filed page. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalChiralNonfreeNominatedVote
open Function Filter Finset RG Lattice Wilson Source Labels Next.Rank Next.Rank.Price Next.Rank.Atlas
open Next.Rank.Station Further.CorrectedLift Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonMaxwellThermometerMaximalHead WilsonOriginalMicroscopicGuardedPage RG05Readout.Address
open WilsonMeasuredPublicEntranceGridDebit Trace.Physical Push.RelayDifference Bandage
open WilsonPositionCapTransport WilsonMaxwellThermometerNominatedOrientation
open Spec OPE OPE.Orbits RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize
open WilsonPhysicalChiralNonfreeStationMoney
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){f:Extraction.Order}{l:Ultrafilter (ℕ×ℕ)}
    {H:(Bel R.family.book).Hierarchy}{S:Table R.family.book}
local notation "C" => R.family

theorem reported (simple:G.Simple)(A:ℝ→Group C 6)(T:ℝ→tower S)
    (book:Book (f:=f) (l:=l) (H:=H) A T){ε:ℝ}(ep:0<ε):
    ∀ᶠ r in trail, ∀ᶠ z:Cutoffs in f.fuse,∀s (i:Fin 3),
    let V:=A r; let d:=index V (grade i); let k:=V.station.k
    let v:=source C s i; let x:=V.change (grade i) v
    let y:=V.station.wheel.atCut z d x
    let χ:=(shrink C k z.1 z.2)^(d.val/2)/(Station.mag (C).path.levels V.station.b k)^d.val
    let a:=((((C).S.a k:ℂ)^d.val)⁻¹)
    R.t d≤k → (C).ref d≤k → 1≤((C).path.levels.budget k).supportExponent →
    ∀U:(C).label d≃ₗ[ℂ](C).label d,
      error ((C).labels.level d) χ (a • U (U.symm (fitted R d k z.1 z.2 y))) (ladder C d v)<ε:=by
  have dates:Tendsto (fun r=>(A r).station.k) trail atTop:=
    tendsto_atTop.mpr fun k=>(book k).mono fun _ h=>h.1
  have e2:0<ε/2:=half_pos ep
  filter_upwards [inBook R simple A T book e2,(book 0),
    dates.eventually (WilsonPhysicalChiralNonfreeStationSize.original (f:=f) (H:=H) R simple)] with r head checked sized
  let V:=A r
  let k:=V.station.k
  have large : ∀ᶠ z:Cutoffs in f.fuse,k<z.1:=(cutoff_grows f).eventually_gt_atTop k
  refine eventually_all.mpr fun s=>eventually_all.mpr fun i=>?_
  let d:=index V (grade i)
  let v:=source C s i
  let p:=ladder C d (V.change (grade i) v)
  let M:=((C).labels.level d).coeffSize p/(1-WilsonMaxwellThermometerStationHeads.fee R k)
  have small:Tendsto (fun z:Cutoffs=>|levy R d z.1 z.2 k| * M) f.fuse (𝓝 0):=by
    simpa only [abs_zero,zero_mul] using (period R d k f).abs.mul_const M
  filter_upwards [large,small.eventually_lt_const e2] with z live wind
  intro V' d' k' v' x y χ a early ref width U
  let F:=(C).labels.level d
  have size:χ*F.coeffSize (awake C d k z.1 z.2 y)≤M:=
    sized V rfl checked.2.1 z.1 z.2 live s i
  have χ₀:0≤χ:=div_nonneg (pow_nonneg (shrink_pos C R.makes live.le z.2).le _) (pow_nonneg (mag_pos _ _ _).le _)
  have wk:‖(χ:ℂ)*a‖*WilsonPhysicalChiralNonfreeStationVote.wrap R d z.1 z.2 k y< ε/2:=by
    rw [same R d z.1 z.2 k y χ χ₀]
    apply lt_of_le_of_lt _ wind
    exact mul_le_mul (le_abs_self _) size (mul_nonneg χ₀ (Finset.sum_nonneg fun _ _=>norm_nonneg _)) (abs_nonneg _)
  have here:=WilsonPhysicalChiralNonfreeStationVote.filed R d z.1 z.2 k early ref live.le width y U χ (ladder C d v)
  exact here.trans_lt (lt_of_lt_of_le (add_lt_add (head z.1 z.2 live s i) wk) (by linarith))

end YM.Integration.WilsonPhysicalChiralNonfreeNominatedVote
