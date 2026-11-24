import YM.Integration.WilsonOriginalOccupiedClear
import YM.Integration.WilsonOriginalFailedHaloPosterior
import YM.Integration.WilsonOriginalFlatOccupiedRate
import YM.Integration.WilsonThermometerUnitFilingRaw

/-! All ordinary soft faces of the actual capture gallery on any older original flat posterior. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRegular
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm Extra.Histories Multi WilsonCenteredCompleteGallery
open WilsonThermometerUnitFilingCoarse (reading)
open QuadraticLocal.Fusion.Attached Planned.GuardedAtom Comparison.RG02.Cumulants
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}{V X I:Type}[DecidableEq V][Fintype V]
    {o:V→Site n}{J:Census V}{p:BudgetPoint}{w:V→ℝ}

theorem masked (P:Rep G n)(L:Lamps X I G P.p o J)(hw:∀v,0<w v)(regular:L.Paid w P.p.B P.p.supportExponent 1)
    (x:X)(s:J.Mode)(U:Config G n):
    Poly.toll w s * ‖(Poly.pass (L.log x U)).part s‖ ≤ (shards J s).card:=by
  have each(t:Hot J): Poly.toll w t.val * ‖(L.log x U).part t.val‖ ≤ 1:=by
    obtain ⟨v,hv⟩:=t.property
    exact WilsonFirstReceivedGalleryRegular.occupied (P:=P) L regular P.p.exponent_pos.le hw x U t.val v hv
  have shard (q:(parts J).Mode)(ok:q∈shards J s):
      Poly.toll w s*‖∏t∈q.val,(L.log x U).part t.val‖ ≤ 1:=by
    have split : Poly.toll w s=∏t∈q.val,Poly.toll w t.val:=by
      rw [←show unionOf q=s from (mem_filter.mp ok).2]
      exact prod_biUnion (parts_wise q)
    rw [split,norm_prod,←prod_mul_distrib]
    exact prod_le_one (fun t _=>mul_nonneg (Poly.worth hw _).le (norm_nonneg _)) (fun t _=>each t)
  rw [pass_partition _ (L.quiet_of_hasSum x U (regular.sums P.p.exponent_pos.le hw x U))]
  calc
    _ ≤ Poly.toll w s * ∑p∈shards J s,‖∏t∈p.val,(L.log x U).part t.val‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le ..) (Poly.worth hw _).le
    _ = ∑p∈shards J s,Poly.toll w s * ‖∏t∈p.val,(L.log x U).part t.val‖:=mul_sum .. 
    _ ≤ ∑_∈shards J s,(1:ℝ):=sum_le_sum (fun q hq=>shard q hq)
    _ = _:=by simp

theorem measurable [Countable I] (L:Lamps X I G p o J)(x:X)(s:J.Mode):
    Measurable (fun U=>(Poly.pass (L.log x U)).part s):=by
  have logs:Measurable (L.log x):=by
    apply Measurable.tsum (f:=fun i U=>L.frame i x U)
    intro i
    apply (Overlay.Bands.sends _).measurable.comp
    unfold Lamps.light
    split
    · exact (L.legal x i).borel
    · exact masked_measurable _ _ _ (L.legal x i).borel
  exact (Poly.get s).measurable.comp (Poly.pass_cont.measurable.comp logs)

theorem older (R:Run G){N per b i:ℕ}(ib:i ≤ b)(top:b ≤ N)
    {o₁:V→Site (R.family.side b per)}[Countable I](P:Rep G (R.family.side b per))(L:Lamps X I G P.p o₁ J)
    (hw:∀v,0<w v)(paid:L.Paid w P.p.B P.p.supportExponent 1)(x:X)(s:J.Mode):
    Poly.toll w s*‖actualTransport R.family (N:=N) (fun U=>(Poly.pass (L.log x U)).part s) ib 1‖ ≤
      (shards J s).card:=by
  let F:=fun U=>(Poly.pass (L.log x U)).part s
  have wp:=Poly.worth hw s
  have roof:∀U,‖F U‖ ≤ ((shards J s).card:ℝ)/Poly.toll w s:=
    fun U=>(le_div_iff₀ wp).mpr ((mul_comm ..).trans_le (masked P L hw paid x s U))
  by_cases eq:i=b
  · subst b
    rw [actualTransport_base R.family R.makes top]
    exact masked P L hw paid x s 1
  have step:i+1≤b:=Nat.succ_le_of_lt (lt_of_le_of_ne ib eq)
  let μ:=WilsonMacroscopicRichFlatPosteriorLaw.law R N per step 1
  letI:IsProbabilityMeasure μ:=WilsonMacroscopicRichFlatPosteriorLaw.prob R step top 1
  letI:IsProbabilityMeasure (scene R.family.path N per b):=probability R.makes.wilson top
  have funds:Integrable F (scene R.family.path N per b):=
    Integrable.of_bound (measurable L x s).aestronglyMeasurable _ (ae_of_all _ roof)
  have expectation:‖∫U,F U ∂μ‖ ≤ ((shards J s).card:ℝ)/Poly.toll w s:=by
    simpa using norm_integral_le_of_norm_le_const (μ:=μ) (ae_of_all _ roof)
  change Poly.toll w s*‖actualTransport R.family (N:=N) F ib 1‖ ≤ _
  rw [WilsonOriginalFailedHaloPosterior.flat R step top F funds]
  exact (mul_comm ..).trans_le ((le_div_iff₀ wp).mp expectation)

end YM.Integration.WilsonOriginalTwoFlatRegular
end
