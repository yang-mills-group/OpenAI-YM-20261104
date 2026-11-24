import YM.Integration.WilsonThermometerOrdinaryPanelElection
import YM.Integration.WilsonThermometerWeakMixedBoard
import YM.Integration.WilsonThermometerSmallPanelMoment

/-! A genuine preceding weak station and the crossing panels on one physical Wilson calendar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOrdinaryPanels
open Function Filter Set Lattice RG Wilson Spec Extraction Cells
open YM.Integration.WilsonLimitConstruction
open PhysicalNext.Repeat.Legato Next.Rank Next.Rank.Tapes.West Next.Rank.East
open PhysicalNext.RankCovariance MergeProof.East Trace.Over
open scoped Topology Classical

variable {G : Gauge}

theorem original (R : Run G) (paid : R2I.RG05Joint.AcrossPanels R.kit) :
    ∃ (K : Binding R.family) (O : HaarBudget G) (z : ℕ → ℝ),
      K.prices = R.metals.K ∧
      (∀ i d, i ≤ d → MergeProof.Accent.generator G i ≤ z d) ∧
      (∀ d, FiresSky K R.makes O (Next.Foundations.chart G) d (z d)) ∧
      RG12Supply K R.makes O (Next.Foundations.chart G) := by
  obtain ⟨O,z,hz,issued⟩ := paid
  have initial := (R.bought R.T R.tuning.receipts R.t R.accepts R.stories
    R.doors R.makes R.carries R.books).1
  obtain ⟨_,_,_,_,_,K,_,rates,_⟩ := initial.reception
  exact ⟨K,O,z,rates,hz,issued R.family rfl K rates R.makes
    (Next.Rank.East.enclosing R.stories initial.freight R.makes)⟩


theorem previous (R:Run G) (simple:G.Simple) {K:Binding R.family} {O:HaarBudget G}
    (ord:RG12Supply K R.makes O (Next.Foundations.chart G)) (d:ℕ) :
    ∃ (P:Fin 3 → Tapes.Panel d) (ξ:ℝ),
      Checks (P 0).arc (P 1).arc (P 2).arc ξ (trays d) d ∧
      ∀ (n:ℕ) (ε:ℝ), 0 < ε → ∀ᶠ k:ℕ in atTop, ∃ w:ℕ,
        n ≤ w ∧ w ≤ k ∧ R.family.S.a w / R.family.S.a k ≤ R.family.path.levels.clock.hatBeta k ^ ε ∧
        ∃ t, Poised P K R.makes O (Next.Foundations.chart G) (trays d) (ParcelPrice G d) w t := by
  obtain ⟨P,⟨ξ,checks⟩,h⟩ := ord.covers d
  refine ⟨P,ξ,checks,?_⟩
  intro n ε ep
  obtain ⟨l,hl⟩ := exists_nat_ge (2/ε)
  filter_upwards [h n, R.family.path.levels.fits.deep.eventually_ge_atTop l,
    RG05Readout.Many.theta_up (C:=R.family) 1 simple] with k hk floor hot
  obtain ⟨w,low,up,rent,t,poised⟩ := hk
  have le : (l:ℝ) ≤ R.family.path.levels.clock.J k := by exact_mod_cast floor
  have frac : 2*PhysicalNext.InteractingRank.Soft.RG12.dialPower (R.family.path.levels.clock.J k) ≤ ε := by
    change 2*((R.family.path.levels.clock.J k:ℝ)+1)⁻¹ ≤ ε
    rw [← div_eq_mul_inv,div_le_iff₀ (by positivity)]
    have num := (div_le_iff₀ ep).mp hl
    linarith [mul_le_mul_of_nonneg_right le ep.le]
  exact ⟨w,low,up,rent.trans (Real.rpow_le_rpow_of_exponent_le hot frac),t,poised⟩

end YM.Integration.WilsonThermometerOrdinaryPanels
