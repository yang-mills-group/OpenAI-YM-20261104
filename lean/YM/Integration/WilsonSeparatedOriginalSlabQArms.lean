import YM.Integration.WilsonReportingPrescribedOldScale
import YM.Integration.WilsonReportHarvestSlabSingletonBasis
import YM.Integration.WilsonReportingPrescribedOldUnitProbes

/-! Period-independent bounds on the actual calibrated microscopic observable at all configurations. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabQArms
open Function Filter Finset Lattice Wilson RG Tree Precision Source Labels
open PhysicalNext.Repeat.Legato RGComparison.Core16 RGComparison.Core16.Spool
open MS MS.Rake MS.Menus MS.Local.Physical Extra.Histories RG05Readout RG05Readout.Native
open scoped Classical Topology BigOperators

variable {G:Gauge}(R:Run G){B:Deck G}(Q:MS.Land.Prescription B){I:Type*}[Fintype I]
    (u:I→Label B)(K:ℕ)(μ:ℝ)

theorem fixed:
    ∃C:ℝ,0<C ∧ ∃d:ℕ,∀(i:I)(k:ℕ),k≤K→∀(t:ℝ)(n:Side)(x:Site n)(U:Config G n),
      ‖ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) (μ-t) n x U k‖≤C*(1+‖t‖)^d:=by
  obtain ⟨P,pp,d,fees⟩:=ActualOriginalFeeGrowth.shifted_bound B Q u K μ
  have basis (i:I)(g:Glyph B (u i).h):∃c:ℝ,0≤c ∧ ∀V:CoverConfig G,
      ‖(R.family.localSection g.size).evaluate (ActualOriginalDictionary.coordinates R B g.size g.grade g.2.2) V‖≤c:=by
    obtain ⟨b,priced⟩:=(Envelope.compactC ((R.family.localSection g.size).continuous_evaluate
      (ActualOriginalDictionary.coordinates R B g.size g.grade g.2.2))).cost
    exact ⟨max 0 b,le_max_left ..,fun V=>(priced V).trans (le_max_right ..)⟩
  choose a positive bound using basis
  let A:=max 1 (∑i,∑g,a i g)
  have pos:0<A:=lt_of_lt_of_le zero_lt_one (le_max_left ..)
  refine ⟨P*A,mul_pos pp pos,d,?_⟩
  intro i k hk t n x U
  rw [ActualOriginalCalibratedColumns.weighted_observable_original]
  let clock:=P*(1+‖t‖)^d
  have nonneg:0≤clock:=mul_nonneg pp.le (pow_nonneg (by positivity) _)
  have cost:(∑g,a i g)≤A:=(single_le_sum (f:=fun v=>∑g,a v g) (fun v _=>sum_nonneg fun g _=>positive v g) (mem_univ i)).trans (le_max_right ..)
  calc
    _ ≤ ∑g:Glyph B (u i).h,clock*a i g := (norm_sum_le ..).trans (sum_le_sum fun g _=>by
      rw [norm_mul]
      exact mul_le_mul (fees i k hk g t) (bound i g (expandAt x U)) (norm_nonneg _) nonneg)
    _ = clock*(∑g,a i g) := (mul_sum ..).symm
    _ ≤ clock*A := mul_le_mul_of_nonneg_left cost nonneg
    _ = _ := by dsimp [clock];ring

theorem original (hG:G.Simple):
    ∃C:ℝ,0<C ∧ ∃d:ℕ,∀ᶠj:ℕ in atTop,∀{m t:ℕ},j≤t→WilsonReportHarvestUpperRange.eligible R.family.S m j t→
      ∀(i:I)(k:ℕ),k≤K→∀(n:Side)(x:Site n)(U:Config G n),
        ‖ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) (μ-R.family.S.scale (t+1)) n x U k‖≤
          C*(R.family.path.levels.clock.hatBeta j)^d:=by
  obtain ⟨P,pp,d,atoms⟩:=fixed R Q u K μ
  obtain ⟨a,ap,dated⟩:=WilsonReportingPrescribedOldScale.clock R hG
  refine ⟨P*a^d,mul_pos pp (pow_pos ap d),d,?_⟩
  filter_upwards [dated] with j sale
  intro m t jt round i k hk n x U
  refine (atoms i k hk _ n x U).trans ?_
  have issued:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0≤1+‖R.family.S.scale (t+1)‖ by positivity) (sale jt round) d) pp.le
  simpa only [mul_pow,mul_assoc] using issued

end YM.Integration.WilsonSeparatedOriginalSlabQArms
