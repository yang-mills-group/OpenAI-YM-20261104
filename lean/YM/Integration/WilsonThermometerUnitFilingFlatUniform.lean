import YM.Integration.WilsonThermometerUnitFilingFlatOffer
import YM.Integration.WilsonThermometerUnitFilingChartFee
import YM.Integration.WilsonThermometerUnitFilingWindowCost

/-! A full true conditional at the short stop, from one stored upper pupil and its genuinely coissued dated debits. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFlatUniform
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonCenteredFiledAtoms WilsonThermometerUnitFilingFlatCourse WilsonThermometerUnitFilingFlatTelescope
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingWindowCost Pert.Asymptotics
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple) (way:WayStation R.kit)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (ticket:TicketP R.alloy R.kit D Q)
local notation "C" => R.family
local notation "hat!" i:max => (C).path.levels.clock.hatBeta i
local notation "σ" => (C).S.scale

include simple way D Q ticket in
theorem original : ∃u₀:ℕ,∀{K:ℝ},0≤K → ∀ᶠ b:ℕ in atTop,∀v:ℕ,u₀≤v → ∀ vb:v≤b,
    σ b-σ v ≤ K*Real.log (4*(hat! b))+(1+Real.log (hat! b)) →
    ∀{N per m k:ℕ},b<N → m≤v → ∀ (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ →
    ∀(rows:∀j:ℕ,Config G (R.family.side j per)→ℂ) (places:∀j,Site (R.family.side j per))
      (q d:ℕ) {B:ℝ},0≤B →
    ∀{M:ℝ},Store ((C).path.rep N per b) ((C).localSection 0) (C).params (places b)
        (LocalComparison.forcedDivisor (C) b) M (numerator R N per b (rows b)) →
    (∀j∈Ico v b,Entered R N Ψ rows j d (places j) (B*(regulatorRun C N per (j-1))^(order q d))) →
    ‖reading R (N:=N) (numerator R N per b (rows b)) v vb-rows v 1‖ ≤
      ((6+WilsonThermometerUnitFilingFieldRange.basisCost G d)*B)*
        (price q d K*(regulatorRun C N per (b+1))^q):=by
  obtain ⟨u,clock⟩:=WilsonThermometerUnitFilingWindowCost.original R simple
  let first:=WilsonSingleHardRadius.start R simple 0 (zero_lt_one:0<(1:ℝ))
  refine ⟨max u first,?_⟩
  intro K kp
  filter_upwards [clock kp] with b meter
  intro v spot vb short N per m k live floor π Γ Ψ course rows places q d B bp M top entered
  have gate:first ≤ v:=(le_max_right u first).trans spot
  have series:=meter v ((le_max_left u first).trans spot) vb short N per live q d
  let bills:=fun j=>B*(regulatorRun C N per (j-1))^(order q d)
  have born:=WilsonThermometerUnitFilingFlatOffer.stored R rows live.le top
  have offered:=WilsonThermometerUnitFilingFlatOffer.original R rows π Γ Ψ course (fun _=>d) places bills
    floor live.le entered born
  have realSum:=WilsonThermometerUnitFilingFlatCourse.original R π Γ Ψ course rows simple way D Q ticket live.le floor vb gate
    (fun _=>d) places bills offered entered
  let bound:=6+WilsonThermometerUnitFilingFieldRange.basisCost G d
  have basisp:0 ≤ WilsonThermometerUnitFilingFieldRange.basisCost G d:=
    zero_le_one.trans (Next.Foundations.full_value_bound (G:=G) d).choose_spec.1
  have bounded:0 ≤ bound:=by dsimp [bound];positivity
  calc _ ≤ ∑j∈Ico v b,(WilsonThermometerUnitFilingFieldRange.cost G d (Ψ j).p.threshold+5)*(bills j):=realSum
       _≤ ∑j∈Ico v b,(bound*B)*((hat! j)^d*(regulatorRun C N per (j-1))^(order q d)):=by
        apply sum_le_sum
        intro j jmem
        have residence:=mem_Ico.mp jmem
        have step:=WilsonThermometerUnitFilingChartFee.original R π Γ Ψ course d (floor.trans residence.1)
          (residence.2.le.trans live.le)
        have gpos:0 ≤ regulatorRun C N per (j-1):=inv_nonneg.mpr (Real.sqrt_nonneg _)
        have loan:0≤bills j:=mul_nonneg bp (pow_nonneg gpos _)
        refine (mul_le_mul_of_nonneg_right step loan).trans_eq ?_
        dsimp [bound,bills];ring
       _ = (bound*B)*(∑j∈Ico v b,(hat! j)^d*(regulatorRun C N per (j-1))^(order q d)):=by rw [mul_sum]
       _≤_:=mul_le_mul_of_nonneg_left series (mul_nonneg bounded bp)

end YM.Integration.WilsonThermometerUnitFilingFlatUniform
