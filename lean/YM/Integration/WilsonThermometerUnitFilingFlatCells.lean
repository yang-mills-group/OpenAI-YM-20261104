import YM.Integration.WilsonThermometerUnitFilingFlatUniform
import YM.Integration.WilsonThermometerUnitFilingRawSum
import YM.Integration.WilsonThermometerSupportedCells

/-! The compact thermometer pupil follows its genuine cellwise appointments in the same earlier conditional law. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFlatCells
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonCenteredFiledAtoms WilsonThermometerUnitFilingFlatCourse WilsonThermometerUnitFilingFlatTelescope
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingWindowCost Pert.Asymptotics
open Cells RG12 XSpace WilsonThermometerAlignedCells
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "hat!" i:max => (C).path.levels.clock.hatBeta i
local notation "σ" => (C).S.scale

abbrev CellsAt (N p:ℕ) (r:ℝ) (φ:Test 3):=WilsonThermometerSupportedCells.Occupied (N:=N) (per:=p) R r φ
def weights {N per:ℕ} {r:ℝ} {φ:Test 3} (c:CellsAt R N per r φ):ℂ:=mass (R:=R) r (N,per) φ c.val
variable {N per b v:ℕ} {r:ℝ} {φ:Test 3} (vb:v≤b)
local notation "Z" => CellsAt R N per r φ

theorem placed (upper:Z → Config G (R.family.side b per) → ℂ) (lower:Z → ℂ) (fee:Z → ℝ)
    (paid:∀c,Integrable (numerator R N per b (upper c)) (prior G _))
    (heard:∀c,‖reading R (N:=N) (numerator R N per b (upper c)) v vb-lower c‖≤fee c):
    ‖reading R (N:=N) (numerator R N per b (fun U=>∑c:Z,weights R c*upper c U)) v vb-
      ∑c:Z,weights R c*lower c‖ ≤ ∑c:Z,‖weights R c‖*fee c:=by
  classical
  let n:=fun c:Z=>numerator R N per b (upper c)
  have joined:numerator R N per b (fun U=>∑c:Z,weights R c*upper c U)=∑c:Z,weights R c • n c:=by
    funext U
    simp only [numerator,n,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply sum_congr rfl
    intro c _
    ring
  have complete:=WilsonThermometerUnitFilingRawSum.family R (N:=N) univ (weights R) n paid vb
  rw [joined,complete.2,←sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum ?_)
  intro c _
  rw [←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left (heard c) (norm_nonneg _)

variable (simple:G.Simple) (way:WayStation R.kit)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (ticket:TicketP R.alloy R.kit D Q)

include simple way D Q ticket in
theorem original : ∃u₀:ℕ,∀{K:ℝ},0≤K  → ∀ᶠ i:ℕ in atTop,∀ (u : ℕ), u₀ ≤ u  → ∀ (ui : u ≤ i),
    σ i-σ u ≤ K*Real.log (4*(hat! i))+(1+Real.log (hat! i))  → 
    ∀{cut side m k:ℕ},i<cut  →  m≤u  → ∀ (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j side)),
    Concourse R.alloy R.kit R.T π Γ m cut side k Ψ  → 
    ∀(radius:ℝ) (profile:Test 3),
    let S:=CellsAt R cut side radius profile
    ∀(rows:S → ∀j:ℕ,Config G (R.family.side j side) → ℂ) (places:S → ∀j,Site (R.family.side j side))
      (q d:ℕ) {B:ℝ},0≤B  → 
    (∀c:S,∃M:ℝ,Store ((C).path.rep cut side i) ((C).localSection 0) (C).params (places c i)
        (LocalComparison.forcedDivisor (C) i) M (numerator R cut side i (rows c i)))  → 
    (∀c:S,∀j∈Ico u i,Entered R cut Ψ (rows c) j d (places c j)
      (B*(regulatorRun C cut side (j-1))^(order q d)))  → 
    ‖reading R (N:=cut) (numerator R cut side i (fun U=>∑c:S,weights R c*rows c i U)) u ui-
      ∑c:S,weights R c*rows c u 1‖ ≤ (∫x:Points 3,‖profile x‖)*
      (((6+WilsonThermometerUnitFilingFieldRange.basisCost G d)*B)*
        (price q d K*(regulatorRun C cut side (i+1))^q)):=by
  obtain ⟨u₀,schedule⟩:=WilsonThermometerUnitFilingFlatUniform.original R simple way D Q ticket
  refine ⟨u₀,?_⟩
  intro K kp
  filter_upwards [schedule kp] with i quote
  intro u opened ui span cut side m k lower floor π Γ Ψ course radius profile S rows places q d B bp top signed
  let V:=((6+WilsonThermometerUnitFilingFieldRange.basisCost G d)*B)*
        (price q d K*(regulatorRun C cut side (i+1))^q)
  have fee:0≤V:=by
    have c:0 ≤ WilsonThermometerUnitFilingFieldRange.basisCost G d:=
      zero_le_one.trans (Next.Foundations.full_value_bound (G:=G) d).choose_spec.1
    have g:0 ≤ regulatorRun C cut side (i+1):=inv_nonneg.mpr (Real.sqrt_nonneg _)
    dsimp [V,price];positivity
  have raw:∀c:S,Integrable (numerator R cut side i (rows c i)) (prior G _):=by
    intro c
    obtain ⟨_,pr⟩:=top c
    exact WilsonThermometerUnitFilingFlatOffer.stored R (rows c) lower.le pr
  have each:∀c:S,‖reading R (N:=cut) (numerator R cut side i (rows c i)) u ui-rows c u 1‖ ≤ V:=by
    intro c
    obtain ⟨_,pr⟩:=top c
    exact quote u opened ui span lower floor π Γ Ψ course (rows c) (places c) q d bp pr (signed c)
  have integrated:=placed R (N:=cut) ui (fun c:S=>rows c i) (fun c:S=>rows c u 1) (fun _=>V) raw each
  refine integrated.trans ?_
  rw [←sum_mul]
  exact mul_le_mul_of_nonneg_right (WilsonThermometerSupportedCells.variation R radius profile) fee

end YM.Integration.WilsonThermometerUnitFilingFlatCells
