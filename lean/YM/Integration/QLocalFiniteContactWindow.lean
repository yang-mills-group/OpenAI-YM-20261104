import YM.Integration.QLocalKineticOrderRestriction
import YM.Integration.QLocalKineticMeshPower
import YM.Integration.WilsonLimitConstruction.FundedCoverKineticQuote
import YM.Integration.ActualNumericCouplingSmallness

/-! The authentic finite-to-cover bond contact is sufficient for the entire
lower kinetic reading on the original measured Wilson background. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalFiniteContactWindow

open Filter Lattice Wilson RG Marker Precision LocalComparison
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 QLocalVacuumOrderRestriction
open AnalyticBridge.VerifiedReset.Averaging WilsonLimitConstruction Pert.Asymptotics
open scoped Classical Topology

variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {J:Request V}
    (R:Run G) (hG:G.Simple) (hT:ActualRunNativeComponentRecipe.Attached R)
    (readout:RG05Preconstruction.ReadoutPurchase R.b)
    (caps:Handoff.OutputCapacities) (A:NumericSchedule R.family J) (K:NumericPrices A)

include hT readout

theorem selected {p:ℕ} (hp:2≤p) (hq:p≤J.order) :
    ∃ C:ℝ,0<C ∧ ∃ s:ℕ,∀ᶠ m:ℕ in atTop,
      ∀ (z:LocalFormal.Datum R.family Γ),z.level=m →
      ∀ (Y:Bulk.Chain R.family.path) (F:AnalyticInput J A z) (η:ℝ) (I:FullPreparedInputAt F η)
        (M:FundedPhysicalCatalogue.Purchase caps K F),
      FundedCoverKineticMeasurement.Tested R Y F M hG (fun v=>(0:(J.tests v).Mood)) →
      ∀ S:FundedRenderedBank.Chosen K I M.toCatalogue,
      η≤(Currency.g R.family z.cutoff z.period (z.level+1))^2 →
      I.carrier.rep.eval=(R.family.path.rep z.cutoff z.period (z.level+1)).eval →
      let f:=regulatorRun R.family z.cutoff z.period (z.level+1)
      let b:=R.family.path.β z.cutoff z.period z.level
      let x:=(plan M.plan p).predict z.level+delta (S.vacuum.listing.read S.vacuum.source)
      0<b ∧ x∈Currency.stripe b ∧ b⁻¹*|x-b|≤6*(C*A.admittedCost m^s*f^(p+1)) := by
  obtain ⟨D,hD,s,degree⟩:=QLocalKineticOrderRestriction.cover (Γ:=Γ) R hG hT A K caps hp hq
  let C:=(3/2:ℝ)^p+D
  have hc:0<C:=by dsimp [C]; positivity
  refine ⟨C,hc,s,?_⟩
  filter_upwards [degree,FundedCoverKineticQuote.reset_defect (Gamma:=Γ) R hG hT readout caps A K p,
    QLocalKineticMeshPower.requested R hG p,QLocalKineticMeshPower.physicalInverse R hG,
    ActualNumericCouplingSmallness.eventually_cost_coupling_small R hG A C hc.le s (1/16) (by norm_num),
    (tendsto_add_atTop_nat 1).eventually (Currency.g_small hG R.makes 1 zero_lt_one)]
    with m low high mesh ratio paid small z hz Y F η I M contact S hη hI
  subst m
  let f:=regulatorRun R.family z.cutoff z.period (z.level+1)
  let b:=R.family.path.β z.cutoff z.period z.level
  let hi:=M.plan.predict z.level
  let lo:=(plan M.plan p).predict z.level
  let d:=delta (S.vacuum.listing.read S.vacuum.source)
  let w:=A.admittedCost z.level
  have hb:0<b:=Overlay.beta_positive R.makes.wilson z.below.le
  have hf:0<f:=Currency.g_pos R.makes _ _ _ (Nat.succ_le_of_lt z.below)
  have coarse:=high z rfl Y F η I M contact S hη hI
  have fine:=low z rfl Y F M contact
  have step:=mesh z.cutoff z.period z.below
  have fw:0≤w^s:=pow_nonneg (A.admitted_cost_nonnegative _) _
  have wone:1≤w^s:=one_le_pow₀ (A.admitted_cost_ge_one _)
  have dx:|lo+d-b|≤|hi+d-b|+|hi-lo|:=by
    have eq:lo+d-b=(hi+d-b)+(lo-hi):=by ring
    rw [eq]
    exact (abs_add_le _ _).trans_eq (congrArg (|hi+d-b|+·) (abs_sub_comm lo hi))
  have amount:|lo+d-b| * f^2≤C*w^s*f^(p+1):=by
    calc
      _≤(|hi+d-b|+|hi-lo|)*f^2:=mul_le_mul_of_nonneg_right dx (sq_nonneg _)
      _=|hi+d-b| * f^2+|hi-lo| * f^2:=add_mul .. 
      _≤(3/2:ℝ)^p*f^(p+1)+D*w^s*f^(p+1):=
        add_le_add ((mul_le_mul_of_nonneg_right coarse (sq_nonneg _)).trans step) fine
      _≤(3/2:ℝ)^p*w^s*f^(p+1)+D*w^s*f^(p+1):=add_le_add
        (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (show 0≤(3/2:ℝ)^p by positivity) wone) (pow_nonneg hf.le _)) le_rfl
      _=_:=by dsimp [C]; ring
  have rel:b⁻¹*|lo+d-b|≤6*(C*w^s*f^(p+1)):=by
    calc
      _≤(6*f^2)*|lo+d-b|:=mul_le_mul_of_nonneg_right (ratio z.cutoff z.period z.below) (abs_nonneg _)
      _=6*(|lo+d-b| * f^2):=by ring
      _≤_:=mul_le_mul_of_nonneg_left amount (by norm_num)
  have f1:f≤1:=(small z.cutoff z.period (Nat.succ_le_of_lt z.below)).le
  have power:f^(p+1)≤f^2:=pow_le_pow_of_le_one hf.le f1 (by omega)
  have last:C*w^s*f^(p+1)≤1/16:=(mul_le_mul_of_nonneg_left power (mul_nonneg hc.le fw)).trans
    (paid z.cutoff z.period z.below)
  have frac:b⁻¹*|lo+d-b|≤1/2:=by linarith only [rel,last]
  have bound:=mul_le_mul_of_nonneg_left frac hb.le
  rw [←mul_assoc,mul_inv_cancel₀ hb.ne',one_mul] at bound
  have both:=abs_le.mp bound
  exact ⟨hb,⟨by linarith only [hb,both.1],by linarith only [hb,both.2]⟩,rel⟩

end YM.Integration.QLocalFiniteContactWindow
