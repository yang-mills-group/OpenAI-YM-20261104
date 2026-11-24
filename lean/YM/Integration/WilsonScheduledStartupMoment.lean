import YM.Integration.WilsonStartupJointMoment
import YM.Integration.WilsonPointStartupPrice
import YM.Integration.WilsonStartupClock

/-! Paid polynomial growth for the genuine fixed-Q signed physical start on
the original clock, before all remaining regulators and locations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonScheduledStartupMoment
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison
open IterationFour IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep
open MergeProof MergeProof.Accent
open scoped Classical BigOperators Topology
variable {G : Gauge} {B : MS.Local.Physical.Deck G} {V : Type} [DecidableEq V] [Fintype V]
    (R : Run G) (hG : G.Simple) (Q : MS.Land.Prescription B) (u : V → MS.Rake.Label B)
    (J : Request V) (K : ℕ) (μ : ℝ)

include hG in
/-- All native fields in an arbitrary signed multimode readout share one
cutoff-uniform polynomial and its true scalar dual invoice. -/
theorem complete : ∃ A : ℝ, 0 < A ∧ ∃ q : ℕ, ∀ᶠ m : ℕ in atTop,
    ∀ (p : ℕ) (o : V → Site (R.family.side (m+1) p)) (orders : V → ℕ), (∀ i, orders i ≤ K) →
    ∀ c : V → ℂ, (∀ i, ‖c i‖ ≤ 1) →
    let D := ActualOriginalQPointSetup.pointDatum R J p (m+1) o
    ∀ (x : IndependentTests (ActualRunQlocalNativeTuple.orbit D)) (ℓ : (Stock.census V).Mode → ℂ),
      let g := WilsonStartupJointMoment.field Q D u (μ-R.family.S.scale (m+1)) orders ℓ
        (VariableScaling.tests c (testInclusion _ x))
      let B := A*R.family.path.levels.clock.hatBeta m^q*(∑ s,‖ℓ s‖)
      (∀ U, ‖g U‖ ≤ B) ∧ ∀ W, ‖actualAverage R.family (N:=m+1) g W‖ ≤ B := by
  obtain ⟨a,ha,q,hq⟩ := WilsonPointStartupPrice.product Q u R J K μ
  obtain ⟨b,hb,ht⟩ := WilsonStartupClock.growth R hG
  refine ⟨a*b^q,mul_pos (zero_lt_one.trans_le ha) (pow_pos hb _),q,?_⟩
  filter_upwards [ht] with m hm
  intro p o orders hk c hc
  dsimp only
  intro x ℓ
  let D := ActualOriginalQPointSetup.pointDatum R J p (m+1) o
  let g := WilsonStartupJointMoment.field Q D u (μ-R.family.S.scale (m+1)) orders ℓ
    (VariableScaling.tests c (testInclusion _ x))
  let B := (a*b^q)*R.family.path.levels.clock.hatBeta m^q
  have H (s : (Stock.census V).Mode) (U : Config G (R.family.side (m+1) p)) :
      ‖ActualStartupNormalizedQ.modeObservable Q D u (μ-R.family.S.scale (m+1)) orders
        (VariableScaling.tests c (testInclusion _ x)) s U‖ ≤ B := by
    refine (hq m p o (R.family.S.scale (m+1)) orders hk c hc x s U).trans ?_
    calc _ ≤ a*(b*R.family.path.levels.clock.hatBeta m)^q :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hm q) (zero_le_one.trans ha)
         _ = B := by dsimp only [B]; rw [mul_pow,mul_assoc]
  have raw (U : Config G (R.family.side (m+1) p)) : ‖g U‖ ≤ B*(∑ s, ‖ℓ s‖) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    rw [norm_mul,mul_comm B _]
    exact mul_le_mul_of_nonneg_left (H s U) (norm_nonneg _)
  exact ⟨raw,actualAverage_norm_le R.family R.makes (Nat.lt_succ_self m) raw⟩
end YM.Integration.WilsonScheduledStartupMoment
