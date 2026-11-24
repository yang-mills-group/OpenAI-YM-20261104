import YM.Integration.WilsonInvariantActionCurvatureAmplitude

/-! The lost curvature field lives on the rejected original plots and has a uniform compact amplitude there. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionCurvatureGate
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Marker
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Legato ActualRunPacketRetuning MergeProof.Accent
open ManuscriptQLocalOriginalConditionalTail ManuscriptQLocalIncidentMasks
open Comparison.Density.RenderM MS.Local.Physical
open WilsonInvariantActionFineCurvature WilsonMatrixOriginalIndependentFields
open WilsonMatrixOriginalCurvatureStock WilsonMatrixOriginalCurvatureField
open WilsonMatrixTicketLanesNativePrices WilsonMatrixOriginalIndependentColumns
open WilsonMatrixTicketLanesReportedPivot
open scoped Classical BigOperators Topology
variable {G:Gauge} {B:Deck G} (R:Run G) (simple:G.Simple)
local notation "I" => B.BIndex (4:ℤ) 2
local notation "u" => WilsonReportingPrescribedOldAction.label B
variable (J:Request (B.BIndex (4:ℤ) 2)) (A:NumericSchedule R.family J) (Q:MS.Land.Prescription B) (μ:ℝ)
variable (d:LocalFormal.Datum R.family (Stock.census (B.BIndex (4:ℤ) 2))) (o:Site (R.family.side (d.level+1) d.period))
local notation "k" => d.level+1
local notation "g" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (k)
local notation "H" => ActualOriginalQInitialInput.normalizer (V:=I) R simple (u) J A d Q (fun _=>o)
  (WilsonMatrixTicketLanesSelectedNormalization.stamp (V:=I) R μ d) (fun _=>0)
local notation "P" => ActualOriginalQInitialInput.packets (V:=I) R simple (u) J A d Q (fun _=>o)
  (WilsonMatrixTicketLanesSelectedNormalization.stamp (V:=I) R μ d) (fun _=>0)
local notation "b" => R.family.path.levels.clock.hatBeta (k)
local notation "Y" => Rep.p (R.family.path.rep d.cutoff d.period (k))
local notation "Ω" => Config G (R.family.side (k) d.period)

include simple J A Q μ o in
def rejected : Set (Config G (R.family.side (d.level+1) d.period)) := by
  let z:=WilsonMatrixTicketLanesSelectedNormalization.stamp (V:=B.BIndex (4:ℤ) 2) R μ d
  let packets:=ActualOriginalQInitialInput.packets (V:=B.BIndex (4:ℤ) 2) R simple
    (WilsonReportingPrescribedOldAction.label B) J A d Q (fun _=>o) z (fun _=>0)
  let p:=R.family.path.rep d.cutoff d.period (d.level+1)
  exact ⋃ i:ManuscriptQLocalOriginalConditionalTail.Live packets,
    ManuscriptQLocalIncidentMasks.failed (G:=G) (ManuscriptQLocalOriginalConditionalTail.token packets i).plot p.p.threshold

theorem borel:MeasurableSet (rejected R simple J A Q μ d o):=by
  unfold rejected
  exact MeasurableSet.iUnion fun i=>ManuscriptQLocalIncidentMasks.measured _ _

theorem clear (v:R.family.label 4) (age:R.family.ref 4≤k) (T:Ω)
    (healthy:T∉rejected R simple J A Q μ d o):
    R.family.O (k) d.period (center R (k) d.cutoff d.period v) o T=WilsonInvariantActionFineCurvature.masked R simple J A Q μ d v o T:=by
  apply sub_eq_zero.mp
  rw [difference R simple J A Q μ d v o age T]
  have same:deficit R simple J A Q μ d o T=0:=by
    unfold deficit WilsonInvariantActionFineSource.plain WilsonInvariantActionFineSource.held
    apply sub_eq_zero.mpr
    rw [ManuscriptQLocalOriginalFineMaskLoss.native,ManuscriptQLocalOriginalConditionalTail.physical]
    apply tsum_congr
    intro i
    have hi:T∉failed (G:=G) (ManuscriptQLocalOriginalConditionalTail.token (P) i).plot (Y).threshold:=fun h=>healthy (Set.mem_iUnion.mpr ⟨i,h⟩)
    change Poly.send ((P).mode i) _=Poly.send ((P).mode i) _
    unfold ManuscriptQLocalOriginalConditionalTail.field
    rw [RG.masked_eq _ _ _ _ (show Healthy (Y).threshold (ManuscriptQLocalOriginalConditionalTail.token (P) i).plot T from not_not.mp hi)]
  rw [same]
  apply Finset.sum_eq_zero
  intro i _
  exact mul_zero _

open private YM.Integration.WilsonInvariantActionWithinFine.distance from YM.Integration.WilsonInvariantActionWithinFine
variable {f:Extraction.Order} {S:Table R.family.book} (Φ:Spec.Final R.family f S) (L:RG17.Layout Φ)
  (U:Ultrafilter (ℕ×ℕ)) (cut:(U:Filter (ℕ×ℕ))≤L.lens)

include Φ L U cut

/-- The quota buys the complete lost source uniformly on every physical field before taking either limit. -/
theorem original (e:ℕ):
    ∃C:ℝ,0<C ∧ ∃s:ℕ,∀(d:LocalFormal.Datum R.family (Stock.census (B.BIndex (4:ℤ) 2)))
      (v:R.family.label 4) (o:Site (R.family.side (d.level+1) d.period)) (M:ℝ), 0≤M →
      R.family.ref 4≤d.level+1 →
      (R.family.S.a (d.level+1)^4)⁻¹*Next.UVStress.quota R.family 4 (d.level+1) d.cutoff d.period v≤
        R.family.path.levels.clock.hatBeta (d.level+1)^e*M →
      ∀T, ‖R.family.O (d.level+1) d.period (center R (d.level+1) d.cutoff d.period v) o T-
          WilsonInvariantActionFineCurvature.masked R simple J A Q μ d v o T‖≤
        (rejected R simple J A Q μ d o).indicator
          (fun _=>C*R.family.path.levels.clock.hatBeta (d.level+1)^s*M) T :=by
  obtain ⟨c,cpos,t,radii⟩:=WilsonMatrixTicketLanesSelectedNormalization.purchased R simple (u) J A Q μ 0
  let cost:=WilsonMatrixOriginalIndependentColumns.fare (warehouse R) B 4
  let rows:ℝ:=(Fintype.card I:ℝ)*2^(ActualOriginalQLayout.rankCap R (u))
  have hz:0≤cost:=Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _
  have hrows:0≤rows:=by dsimp only [rows];positivity
  let C:=1+8*cost*c*(rows+rows)
  have Cp:0<C:=by dsimp only [C];positivity
  obtain ⟨τ,climate⟩:=WilsonMatrixTicketLanesReportedMaster.units R (f:=f) U (cut.trans L.certified)
  refine ⟨C,Cp,e+1+t,?_⟩
  intro d v o M Mpos age quota T
  let β:=R.family.path.levels.clock.hatBeta (d.level+1)
  let stamped:=WilsonMatrixTicketLanesSelectedNormalization.stamp (V:=I) R μ d
  let radius:=ActualOriginalQInitialInput.normalizer R simple (u) J A d Q (fun _=>o) stamped (fun _=>0)
  let packet:=ActualOriginalQInitialInput.packets R simple (u) J A d Q (fun _=>o) stamped (fun _=>0)
  let vacuum:=R.family.path.rep d.cutoff d.period (d.level+1)
  let g₀:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
  by_cases enters:T∈rejected R simple J A Q μ d o
  · rw [Set.indicator_of_mem enters]
    let z:=WilsonMatrixTicketLanesSelectedNormalization.stamp (V:=I) R μ d
    let pay:=∑i,‖normalization R (d.level+1)*(stock B (amounts R B (d.level+1) d.period
      (center R (d.level+1) d.cutoff d.period v))).2 i‖
    have thermometer:=WilsonMatrixOriginalGermEntryTariff.funded R B L U cut τ climate (d.level+1) d.cutoff d.period v quota
    have scale:‖normalization R (d.level+1)‖=(R.family.path.levels.clock.threshold (d.level+1)^2)⁻¹*(R.family.S.a (d.level+1)^4)⁻¹:=by
      unfold normalization
      rw [norm_mul,norm_inv,norm_pow,Complex.norm_real,Complex.norm_real,
        Real.norm_of_nonneg (R.family.S.a_pos _).le,Real.norm_of_nonneg (sq_nonneg _),inv_pow,mul_comm]
    have pay_cap:pay≤8*β*(β^e*M*cost):=by
      dsimp only [pay]
      simp only [norm_mul,←Finset.mul_sum,scale]
      exact thermometer
    have bpos:0≤β:=zero_le_one.trans (R.family.path.levels.fits.delayed _).le
    have Hpos:0≤radius:=zero_le_one.trans (le_max_left _ _)
    have paid:=OriginalMarkedBirthStencil.paid R simple (u) J A d Q (fun _=>o) z (fun _=>0)
      OriginalMarkedBirthStencil.mesh g₀
    have plain:=ManuscriptQLocalOriginalFineMaskLoss.original_rows packet paid (unitTest (B:=B) R J) T
    have kept:=ManuscriptQLocalOriginalFineMaskLoss.regular_rows packet paid (unitTest (B:=B) R J) vacuum.p T
    have cap:ManuscriptQLocalOriginalFineMaskLoss.bound packet (budget:=1)=rows:=by
      have rank:packet.rankCap=ActualOriginalQLayout.rankCap R (u):=rfl
      simp only [ManuscriptQLocalOriginalFineMaskLoss.bound,rank,mul_one,rows]
    have lost:Poly.price (fun _:I=>1) (deficit R simple J A Q μ d o T)≤rows+rows:=
      (YM.Integration.WilsonInvariantActionWithinFine.distance _ _).trans (add_le_add (plain.2.trans_eq cap) (kept.2.trans_eq cap))
    have a:=radii d (fun _=>o) (fun _=>0) (fun _=>le_rfl)
    have bill:=gross R simple J A Q μ d v o age T
    change _≤pay*radius*_ at bill
    refine bill.trans ((mul_le_mul (mul_le_mul pay_cap a Hpos (by positivity))
      lost (Poly.nonnegative (fun _:I=>zero_lt_one) _) (by positivity)).trans ?_)
    calc 8*β*(β^e*M*cost)*(c*β^t)*(rows+rows)=
          (8*cost*c*(rows+rows))*β^(e+1+t)*M:=by rw [pow_add,pow_succ];ring
         _ ≤ C*β^(e+1+t)*M:=mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg bpos _)) Mpos
  · rw [Set.indicator_of_notMem enters,clear R simple J A Q μ d o v age T enters,sub_self,norm_zero]

end YM.Integration.WilsonInvariantActionCurvatureGate
