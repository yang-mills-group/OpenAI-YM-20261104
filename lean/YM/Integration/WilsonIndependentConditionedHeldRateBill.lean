import YM.Integration.WilsonIndependentConditionedLocatedPanelPurse
import YM.Integration.WilsonIndependentConditionedFolioClock
import YM.Integration.WilsonIndependentConditionedHeldRateCurrency
import YM.Integration.WilsonInvariantActionPromotedQuota
import YM.Integration.WilsonOriginalTwoFlatIRSocketPower

/-! The supported two-name room has a single reporter tariff for its four actual
boundary bills, uniform in its physical fine cutoff, period, and chosen face. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedHeldRateBill
open Filter Finset Function RG Lattice Wilson Marker Tree QuadraticLocal Multi PhysicalNext.Repeat.Legato
open Pert.Asymptotics XSpace Table Spec Climb Trace.Pilot PhysMS Extraction
open WilsonReceivedChronologicalFixedReserve (terms)
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
open WilsonReceivedCanonicalVersePortfolio (wallet)
open WilsonOriginalTwoFlatIRSocketPower (ceiling)
open WilsonInvariantActionPosition (berth)
open scoped Topology Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 2→ℕ)
local notation "J" => Stock.census (Fin 2)
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "σ" => R.family.S.scale

def interior (A P:ℕ)(θ:ℝ)(S:(J).Mode):ℝ:=
  (4*((2*A:ℕ):ℝ)/Real.log 3)*WilsonReceivedChronologicalLastFlat.wage S P 1 θ

def terminal (d:Fin 2→ℕ)(P E:ℕ)(C:ℝ):ℝ:=
  ceiling 2 (terms d (fun _=>0) P).order (∑i,d i) E (Fintype.card (Multi.Hot (J))) C

def basal (P:ℕ)(θ:ℝ)(S:(J).Mode):ℝ:=WilsonOriginalOneArmClearCash.wage S P θ

def high (P:ℕ)(η:ℝ)(S:(J).Mode):ℝ:=WilsonReceivedChronologicalLastFlat.wage S P 1 η

def bill (A P E promised goal:ℕ)(C θ η g:ℝ)(S:(J).Mode):ℝ:=
  interior A P θ S*g^promised + terminal d P E C*g^goal +
    basal P θ S*g^P + high P η S*g^P

private def prices (A P E:ℕ)(C θ η:ℝ)(S:(J).Mode):ℝ:=
  |interior A P θ S| + |terminal d P E C| + |basal P θ S| + |high P η S|

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (b:ℝ)(positive:0 ≤ b)(p₀ target reserve old A P E promised goal:ℕ)
    (C θ η:ℝ)(hp:target+4*p₀ ≤ P)(hh:target+4*p₀ ≤ promised)(hg:target+4*p₀ ≤ goal):
    ∃c:ℝ,0 ≤ c ∧ ∀ᶠ f:ℕ in atTop,
      let K:=berth R reserve f
      ∀{first v N per:ℕ},first ≤ v → v ≤ f → K ≤ N →
        σ K-σ first ≤ (old:ℝ)*(1+Real.log (β v)) → ∀S:(J).Mode,
          wallet R d (fun _=>b*(β K)^p₀) S.val *
            bill d A P E promised goal C θ η (regulatorRun R.family N per v) S ≤
            c*(thermal R f)^target:=by
  classical
  obtain ⟨M,M₁,purse⟩:=WilsonIndependentConditionedLocatedPanelPurse.salaries R d b
  let B:=∑S:(J).Mode,prices d A P E C θ η S
  have pr (S:(J).Mode):0 ≤ prices d A P E C θ η S:=by unfold prices;positivity
  have B₀:0 ≤ B:=Finset.sum_nonneg fun a _=>pr a
  let Z:=M*(2:ℝ)^(2*p₀)*8^(target+4*p₀)
  have M₀:=zero_le_one.trans M₁
  have Z₀:0 ≤ Z:=by dsimp [Z];positivity
  refine ⟨Z*B,mul_nonneg Z₀ B₀,?_⟩
  filter_upwards [WilsonInvariantActionPromotedQuota.retained R simple slow reserve,
    WilsonIndependentConditionedFolioClock.original R simple old] with f ratio clock
  dsimp only
  intro first v N per fv vf kN span S
  let K:=berth R reserve f
  have fk:f ≤ K:=(WilsonInvariantActionPosition.arrival R reserve f).1.le
  have tick:=clock (per:=per) fv vf fk kN span
  have β₁:1 ≤ β K:=(R.family.path.levels.fits.delayed K).le
  have β₀:0 < β f:=zero_lt_one.trans (R.family.path.levels.fits.delayed f)
  have g₀:0 ≤ thermal R f:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have balance:β f*(thermal R f)^2=1:=by
    unfold thermal
    rw [inv_pow,Real.sq_sqrt β₀.le,mul_inv_cancel₀ β₀.ne']
  have due:0 ≤ wallet R d (fun _=>b*(β K)^p₀) S.val:=by
    apply Finset.prod_nonneg
    intro j _
    exact mul_nonneg (Finset.sum_nonneg fun a _=>WilsonReceivedCanonicalVersePortfolio.nonneg _ _ _ _)
      (mul_nonneg positive (pow_nonneg (zero_le_one.trans β₁) _))
  have sale:=WilsonIndependentConditionedHeldRateCurrency.four balance (zero_le_one.trans β₁) g₀
    ratio.1 tick.2 tick.1 due M₀ (purse β₁ p₀ S.val) hh hg hp
    (interior A P θ S) (terminal d P E C) (basal P θ S) (high P η S)
  have price:prices d A P E C θ η S ≤ B:=
    Finset.single_le_sum (f:=prices d A P E C θ η) (fun j _=>pr j) (Finset.mem_univ S)
  exact sale.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left price Z₀) (pow_nonneg g₀ _))

end YM.Integration.WilsonIndependentConditionedHeldRateBill
