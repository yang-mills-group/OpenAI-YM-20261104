import YM.Integration.WilsonInvariantActionWithinFine

/-! Absolute values of the previously prescribed curvature terms on the whole compact gauge space. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionCurvatureAmplitude
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Marker
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Legato ActualRunPacketRetuning MergeProof.Accent
open ManuscriptQLocalOriginalConditionalTail ManuscriptQLocalRawSourceRoot
open Comparison.Density.RenderM MS.Local.Physical
open scoped Classical BigOperators Topology

variable {G:Gauge} {B:Deck G} {V:Type} [DecidableEq V] [Fintype V]
  (R:Run G) (simple:G.Simple) (u:V→MS.Rake.Label B) (J:Request V)
  (A:NumericSchedule R.family J) (Q:MS.Land.Prescription B) (μ:ℝ)

open private YM.Integration.ManuscriptQLocalOriginalFineMaskLoss.charged from YM.Integration.ManuscriptQLocalRawMaskCalendar

/-- Every original compensated token is paid before the choice of cutoff, period, location or field. -/
theorem filed (K:ℕ):
    ∃C:ℝ,0<C ∧ ∃e:ℕ,∀(d:LocalFormal.Datum R.family (Stock.census V))
      (o:V→Site (R.family.side (d.level+1) d.period))(orders:V→ℕ), (∀i,orders i≤K) →
      let z:=WilsonMatrixTicketLanesSelectedNormalization.stamp R μ d
      let P:=ActualOriginalQInitialInput.packets R simple u J A d Q o z orders
      let H:=ActualOriginalQInitialInput.normalizer R simple u J A d Q o z orders
      let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
      ∀x T, Summable (fun i:Live P=>‖P.term (testInclusion _ x) g T i‖) ∧
        H*(∑'i:Live P,‖P.term (testInclusion _ x) g T i‖)≤
          C*R.family.path.levels.clock.hatBeta (d.level+1)^e:=by
  obtain ⟨c,hc,e,buy⟩:=WilsonMatrixTicketLanesSelectedNormalization.purchased R simple u J A Q μ K
  let a:ℝ:=(Fintype.card V:ℝ)*2^(ActualOriginalQLayout.rankCap R u)
  have ha:0≤a:=by dsimp only [a];positivity
  refine ⟨c*max 1 a,mul_pos hc (zero_lt_one.trans_le (le_max_left _ _)),e,?_⟩
  intro d o orders bounded z P H g x T
  have paid:=OriginalMarkedBirthStencil.paid R simple u J A d Q o z orders OriginalMarkedBirthStencil.mesh g
  have rows:=roots P paid
  have charge (i:Live P):‖P.term (testInclusion _ x) g T i‖≤
      fare P (g:=g) (w:=fun _=>1) (width:=(ActualOriginalQInitialInput.schedule R simple u J A).inputWidth d.level) i:=by
    refine (row P paid x i T).trans ?_
    simpa only [base, Poly.toll, Finset.prod_const_one, one_mul] using YM.Integration.ManuscriptQLocalOriginalFineMaskLoss.charged P paid i
  have summ:=rows.2.1.of_nonneg_of_le (fun _=>norm_nonneg _) charge
  refine ⟨summ,?_⟩
  have cap: (∑'i:Live P,‖P.term (testInclusion _ x) g T i‖)≤a:=by
    refine (summ.tsum_le_tsum charge rows.2.1).trans ?_
    have rank : P.rankCap=ActualOriginalQLayout.rankCap R u := rfl
    simpa only [mul_one,rank,a] using rows.2.2
  have Hpos:0≤H:=zero_le_one.trans (le_max_left _ _)
  calc H*(∑'i:Live P,‖P.term (testInclusion _ x) g T i‖) ≤ H*a :=
          mul_le_mul_of_nonneg_left cap Hpos
       _ ≤ (c*R.family.path.levels.clock.hatBeta (d.level+1)^e)*max 1 a :=
          mul_le_mul (buy d o orders bounded) (le_max_right _ _) ha
            (mul_nonneg hc.le (pow_nonneg (zero_le_one.trans (R.family.path.levels.fits.delayed _).le) _))
       _ = _ := by ring

end YM.Integration.WilsonInvariantActionCurvatureAmplitude
