import YM.Integration.WilsonInvariantActionCaptureRun
import YM.Integration.WilsonInvariantActionCaptureCharge
import YM.Integration.WilsonInvariantActionRegisteredTranslate
import YM.Integration.WilsonInvariantActionCapturedCovariance
import YM.Integration.WilsonInvariantActionSeparatedWindow
import YM.Integration.WilsonInvariantActionPromotedPair
import YM.Integration.WilsonReportSeparatedMoments

/-! The complete original two-mark covariance through the promoted spatial capture. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionCapturedPoints
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Marker Multi Labels
open OPE OPE.Therm OPE.Strobe OPE.Strobe.Vista26 Extra.Multi Extra.Histories Push
open MergeProof MergeProof.Accent MergeProof.Ribbons ManyCopies Next.Rank
open Next.Rank.Spindle Planned.GuardedAtom Price PhysicalNext.Repeat.Legato
open RG17 FullVolume Spec Climb Trace.Pilot Next.UVStress RGComparison.Core16
open PhysicalNext.Repeat.Daisy.Charity.RG12 WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonInvariantActionPosition WilsonInvariantActionIntegratedPair WilsonInvariantActionPromotedPair
open WilsonInvariantActionCapturedCovariance
open scoped Topology BigOperators Classical
universe u
variable {G:Gauge} (R:Run G) {per k N:ℕ}
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta

private theorem complete (h:k≤N) (w:R.family.label 4) (o:Site (R.family.side k per))
    (U:Config G (R.family.side k per)):
    Vista26.whole R.family 4 k N per w o U = WilsonInheritedRegisteredField.regular R.makes h w o U:=by
  rw [WilsonInvariantActionRegisteredTranslate.original]
  unfold Vista26.whole indexX
  rw [Ribbons.same R.family k per o]
  rfl

def regularCov (h:k≤N) (v:Fin 2→R.family.label 4) (x:Fin 2→Site (R.family.side N per)):ℂ:=
  let μ:=scene R.family.path N per k
  let Y:=fun j=>WilsonInheritedRegisteredField.regular R.makes h (v j) ((R.family.S.toDepth h per).parent (x j))
  (∫U,Y 0 U*Y 1 U ∂μ)-(∫U,Y 0 U ∂μ)*(∫U,Y 1 U ∂μ)

/-- The same estimate at any genuine reporting date and before every later
cutoff. In particular the promoted date is unnecessary for seats which
are already embedded in the manuscript's logarithmic reporting mesh. -/
theorem at_date (simple:G.Simple) {δ₀:ℝ} {T:Campaign R} (W:Campaign.Pillars R T)
    (funded:FundedOriginalProperties.{u} simple δ₀ W) (subsidy:WilsonReportColumnSubsidy.Eligible R.kit)
    {br:ℕ} (brp:0<br) (e t q:ℕ):
    ∀ᶠ k:ℕ in atTop,∀dis:ℕ,((A).budget k).B^8≤dis → (dis:ℝ)≤β k^e →
    ∀ N per (live:k<N)(x:Fin 2→Site (R.family.side N per)),
      (dis≤WilsonInvariantActionSeparatedCells.gap R.family live.le x ∧
       WilsonInvariantActionSeparatedCells.gap R.family live.le x≤br*dis) →
      ∀v:Fin 2→R.family.label 4,(∀i,quota R.family 4 k N per (v i)≤R.family.S.a k^4*β k^t) →
      ‖posterior R (someSlices (A) per) live.le (v 0) (v 1) (parents R live.le x)-regularCov R live.le v x‖
        ≤ WilsonReportSeparatedMoments.fee census both q*(Pert.Asymptotics.regulatorRun R.family N per k)^(2*q):=by
  have citizen:=WilsonInvariantActionCaptureRun.on_run simple W funded subsidy
  have sale:=WilsonReportSeparatedMoments.purchased simple R.makes funded.2.1.logBudget.money citizen
    census (fun _:Fin 2=>4) brp e t q
  filter_upwards [sale] with k booked dis minD maxD N per live x far v amounts
  let c:Fin 2→Site (R.family.side k per):=fun i=>(R.family.S.toDepth live.le per).parent (x i)
  have u:separation (c 0) (c 1)≤br*dis:=far.2
  have l:dis ≤ separation (c 0) (c 1):=far.1
  have sq:Sites26 (C:=R.family) br dis c:=by
    constructor
    · intro i j
      fin_cases i <;> fin_cases j
      · simp
      · exact u
      · rw [separation_comm];exact u
      · simp
    · intro i j diff
      fin_cases i <;> fin_cases j
      · exact (diff rfl).elim
      · exact l
      · rw [separation_comm];exact l
      · exact (diff rfl).elim
  have reading:=booked dis minD maxD N per live c sq v
    (fun i=>WilsonInvariantActionCaptureCharge.admitted R.family (v i) (amounts i)) both
  change ‖(Extra.Trajectories.connected (WilsonReportMomentDifference.microscopic census R.family
    (BarePack (C:=R.family) (fun _:Fin 2=>4) c live.le v))).part both-
    (Extra.Trajectories.connected (WilsonReportMomentDifference.reported census R.family (N:=N)
      (regularPack (C:=R.family) (N:=N) (fun _:Fin 2=>4) c v))).part both‖≤
    WilsonReportSeparatedMoments.fee census both q*(Pert.Asymptotics.regulatorRun R.family N per k)^(2*q) at reading
  have hiPack:BarePack (C:=R.family) (fun _:Fin 2=>4) c live.le v =
      fun i=>R.family.O N per (v i) (parents R live.le x i):=rfl
  have loPack:regularPack (C:=R.family) (N:=N) (fun _:Fin 2=>4) c v =
      fun i=>WilsonInheritedRegisteredField.regular R.makes live.le (v i) (c i):=by
    funext i U;exact complete R live.le (v i) (c i) U
  rw [hiPack,WilsonInvariantActionCapturedCovariance.original R (someSlices (A) per) live.le,
    loPack,WilsonInvariantActionCapturedCovariance.lower R.family R.makes live.le] at reading
  exact reading

/-- Uniform in every contributing point of the original signed external
test, the two upper physical fields and their complete earlier regular
receipts are compared on the same run, before both microscopic limits. -/
theorem purchased (simple:G.Simple) {δ₀:ℝ} {T:Campaign R} (W:Campaign.Pillars R T)
    (funded:FundedOriginalProperties.{u} simple δ₀ W) (subsidy:WilsonReportColumnSubsidy.Eligible R.kit)
    (pace:WilsonWindowReportingPace.Slow R.kit) {B:ℕ} (hB:0<B) {s:ℕ} (hs:1 ≤ s)
    (t q:ℕ) (φ:Test 2):
    let m:=WilsonMeasuredWindow.stop (A) simple B
    let k:=fun r=>berth R s (m r)
    ∀ᶠ r in trail,∀(hr:0<r) N per (h:k r<N) (x:Fin 2→Site (R.family.side N per)),
      WilsonExternalMeshMass.charge R.family (dilate hr φ) x≠0 → ∀ v:Fin 2→R.family.label 4,
      (∀i,quota R.family 4 (k r) N per (v i)≤R.family.S.a (k r)^4*β (k r)^t) →
      ‖posterior R (someSlices (A) per) h.le (v 0) (v 1) (parents R h.le x)-regularCov R h.le v x‖
        ≤ WilsonReportSeparatedMoments.fee census both q*(Pert.Asymptotics.regulatorRun R.family N per (k r))^(2*q):=by
  let m:=WilsonMeasuredWindow.stop (A) simple B
  let k:=fun r=>berth R s (m r)
  obtain ⟨br,dis,brp,grows,geometry⟩:=WilsonInvariantActionSeparatedWindow.filed R simple pace hB hs φ
    φ.hasCompactSupport φ.tsupport_subset (Subset.rfl)
  have sale:=at_date R simple W funded subsidy brp (s+4) t q
  filter_upwards [geometry,grows.eventually sale] with r geom booked
  intro hr N per live x signed v amounts
  exact booked (dis r) geom.1 geom.2.1 N per live x (geom.2.2 hr N per live.le x signed) v amounts

end YM.Integration.WilsonInvariantActionCapturedPoints
