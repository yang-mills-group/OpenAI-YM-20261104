import YM.Integration.QLocalForecastOrderReadout
import YM.Integration.WilsonLimitConstruction.FundedSignedCoefficientMass

/-! Charge the original selected kinetic polynomial when the order of the same plan is reduced. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalKineticOrderRestriction

open Filter Finset Lattice Wilson RG Marker PhysicalNext.Repeat.Legato
open IterationFour IterationFour.Vacuum LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalVacuumOrderRestriction WilsonLimitConstruction Comparison.RG02 PhysicalWilsonActionConvention Pert.Asymptotics
open FullQLocal.PreRun.CostProfile MatchingLedger.Compass.Income
open scoped Classical Topology BigOperators

variable {G : Gauge} {C : Family G} {N t q : ℕ}

def interval (p q : ℕ) := range (q-2+1) \ range (p-2+1)

theorem split (P : Plan C N t q) (m : ℕ) (g : ℝ) {p : ℕ} (hp : p≤q) :
    P.poly m g-(plan P p).poly m g = ∑ e∈interval p q, P.coefficient m e*g^e := by
  have sub : range (p-2+1)⊆range (q-2+1) := range_mono (by omega)
  have eq := Finset.sum_sdiff (f:=fun e=>P.coefficient m e*g^e) sub
  change (∑ e∈range (q-2+1),P.coefficient m e*g^e) - (∑ e∈range (p-2+1),P.coefficient m e*g^e) = _
  unfold interval
  linarith only [eq]

theorem purchased_power (P : Plan C N t q) (m : ℕ) (g : ℝ) (hg : 0≤g) (hg1 : g≤1)
    {p : ℕ} (hp : 2≤p) (hq : p≤q) :
    |P.poly m g-(plan P p).poly m g| * g^2 ≤
      (1+∑ e∈range (q-2+1),|P.coefficient m e|)*g^(p+1) := by
  have individual (e : ℕ) (he : e∈interval p q) : ‖P.coefficient m e * g^e‖ ≤ |P.coefficient m e| * g^(p-1) := by
    have high := (Finset.mem_sdiff.mp he).2
    have rank : p-1≤e := by simp only [Finset.mem_range,not_lt] at high; omega
    simp only [Real.norm_eq_abs,abs_mul,abs_pow,abs_of_nonneg hg]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hg hg1 rank) (abs_nonneg _)
  have rows := (norm_sum_le (interval p q) (fun e=>P.coefficient m e*g^e)).trans
    (Finset.sum_le_sum individual)
  have subset : interval p q⊆range (q-2+1) := Finset.sdiff_subset
  have sum := Finset.sum_le_sum_of_subset_of_nonneg subset (f:=fun e=>|P.coefficient m e|) (fun e _ _=>abs_nonneg _)
  rw [←Finset.sum_mul,Real.norm_eq_abs,←split P m g hq] at rows
  calc
    _ ≤ ((∑ e∈interval p q,|P.coefficient m e|)*g^(p-1))*g^2 :=
      mul_le_mul_of_nonneg_right rows (sq_nonneg _)
    _ ≤ ((1+∑ e∈range (q-2+1),|P.coefficient m e|)*g^(p-1))*g^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [sum]) (pow_nonneg hg _)) (sq_nonneg _)
    _ = _ := by rw [mul_assoc,←pow_add,show p-1+2=p+1 by omega]

private theorem «partial» (P : Plan C N t q) (m : ℕ) (g : ℝ) (hg : 0≤g) (hg1 : g≤1)
    {p : ℕ} (hq : p≤q) : |(plan P p).poly m g| ≤ 1+∑ e∈range (q-2+1),|P.coefficient m e| := by
  have sub : range (p-2+1)⊆range (q-2+1) := range_mono (by omega)
  have sum := Finset.sum_le_sum_of_subset_of_nonneg sub (f:=fun e=>|P.coefficient m e|) (fun _ _ _=>abs_nonneg _)
  have rows := (norm_sum_le (range (p-2+1)) (fun e=>P.coefficient m e*g^e)).trans
    (Finset.sum_le_sum (fun e _ => show ‖P.coefficient m e*g^e‖≤|P.coefficient m e| by
      rw [Real.norm_eq_abs,abs_mul,abs_pow,abs_of_nonneg hg]; exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hg hg1)))
  exact (by simpa only [Real.norm_eq_abs, Plan.poly, plan] using rows : |(plan P p).poly m g|≤_).trans (by linarith only [sum])

private theorem stripe_of_small {β g z : ℝ} (hg : 0<g) (epoch : β*g^2=1)
    (small : |z| * g^2≤1/2) : β+z∈Currency.stripe β := by
  have limits := abs_le.mp (show |z*g^2|≤1/2 by simpa only [abs_mul,abs_of_nonneg (sq_nonneg g)] using small)
  constructor
  · apply (mul_le_mul_iff_left₀ (pow_pos hg 2)).mp
    linarith only [show (β/4)*g^2=(β*g^2)/4 by ring,show (β+z)*g^2=β*g^2+z*g^2 by ring,epoch,limits.1]
  · apply (mul_le_mul_iff_left₀ (pow_pos hg 2)).mp
    linarith only [show (4*β)*g^2=4*(β*g^2) by ring,show (β+z)*g^2=β*g^2+z*g^2 by ring,epoch,limits.2]

variable {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {J : Request V}
    (R : Run G) (hG : G.Simple) (hT : ActualRunNativeComponentRecipe.Attached R)
    (A : NumericSchedule R.family J) (K : NumericPrices A) (caps : Handoff.OutputCapacities)

include hG hT

theorem stripes {p : ℕ} (hq : p≤J.order) :
    ∀ᶠ m : ℕ in atTop, ∀ (z : LocalFormal.Datum R.family Γ), z.level=m →
      ∀ (Y : Bulk.Chain R.family.path) (F : AnalyticInput J A z) (M : FundedPhysicalCatalogue.Purchase caps K F),
        FundedCoverKineticMeasurement.Tested R Y F M hG (fun v=>(0:(J.tests v).Mood)) →
        let β := R.family.path.β z.cutoff z.period (z.level+1)
        1≤β ∧ M.plan.predict z.level∈Currency.stripe β ∧ (plan M.plan p).predict z.level∈Currency.stripe β := by
  obtain ⟨D,hD,s,bill⟩ := FundedCoverCoefficientMass.mass_polynomial R hG hT (R:=Γ) caps A K
  filter_upwards [bill,ActualNumericCouplingSmallness.eventually_cost_coupling_small R hG A D hD.le s (1/2) (by norm_num),
    (tendsto_add_atTop_nat 1).eventually (Currency.g_small hG R.makes 1 zero_lt_one)]
    with m paid little small z hz Y F M contact
  subst m
  let g := regulatorRun R.family z.cutoff z.period (z.level+1)
  let β := R.family.path.β z.cutoff z.period (z.level+1)
  have hg : 0<g := Currency.g_pos R.makes _ _ _ (Nat.succ_le_of_lt z.below)
  have hβ : 0<β := Weather.iceborn R.family R.makes (Nat.succ_le_of_lt z.below) z.period
  have epoch : β*g^2=1 := Weather.epoch R.family R.makes (Nat.succ_le_of_lt z.below) z.period
  have weak : g≤1 := (small z.cutoff z.period (Nat.succ_le_of_lt z.below)).le
  have mass := paid z rfl Y F M _ contact
  have invoice (r : ℕ) (hr : r≤J.order) : β+(plan M.plan r).poly z.level g∈Currency.stripe β :=
    stripe_of_small hg epoch ((mul_le_mul_of_nonneg_right ((«partial» M.plan z.level g hg.le weak hr).trans mass) (sq_nonneg _)).trans
      (little z.cutoff z.period z.below))
  have one : 1≤β := epoch.symm.le.trans (mul_le_of_le_one_right hβ.le (pow_le_one₀ hg.le weak))
  exact ⟨one,by simpa only [Plan.predict,if_neg (Nat.ne_of_lt z.below), Plan.poly, plan, g, β] using invoice J.order le_rfl,
    by simpa only [Plan.predict,if_neg (Nat.ne_of_lt z.below)] using invoice p hq⟩

/-- The authentic positive kinetic/action contact pays the true beta difference across orders
at both complete radii of the same Run. No independent lower Plan is selected. -/
theorem cover {p : ℕ} (hp : 2≤p) (hq : p≤J.order) :
    ∃ D : ℝ, 0<D ∧ ∃ s : ℕ, ∀ᶠ m : ℕ in atTop,
      ∀ (z : LocalFormal.Datum R.family Γ), z.level=m →
      ∀ (Y : Bulk.Chain R.family.path) (F : AnalyticInput J A z) (M : FundedPhysicalCatalogue.Purchase caps K F),
        FundedCoverKineticMeasurement.Tested R Y F M hG (fun v=>(0:(J.tests v).Mood)) →
        let g := regulatorRun R.family z.cutoff z.period (z.level+1)
        |M.plan.predict z.level-(plan M.plan p).predict z.level| * g^2 ≤ D*A.admittedCost m^s*g^(p+1) := by
  obtain ⟨D,hD,s,bill⟩ := FundedCoverCoefficientMass.mass_polynomial R hG hT (R:=Γ) caps A K
  refine ⟨D,hD,s,?_⟩
  filter_upwards [bill,(tendsto_add_atTop_nat 1).eventually (Currency.g_small hG R.makes 1 zero_lt_one)]
    with m paid small z hz Y F M h
  subst m
  let g := regulatorRun R.family z.cutoff z.period (z.level+1)
  have hg : 0<g := Currency.g_pos R.makes _ _ _ (Nat.succ_le_of_lt z.below)
  have weak : g≤1 := (small z.cutoff z.period (Nat.succ_le_of_lt z.below)).le
  have fine : M.plan.predict z.level-(plan M.plan p).predict z.level = M.plan.poly z.level g-(plan M.plan p).poly z.level g := by
    simp only [Plan.predict,if_neg (Nat.ne_of_lt z.below)]
    change (_+M.plan.poly z.level g)-(_+(plan M.plan p).poly z.level g)=_
    ring
  rw [fine]
  exact (purchased_power M.plan z.level g hg.le weak hp hq).trans
    (mul_le_mul_of_nonneg_right (paid z rfl Y F M _ h) (pow_nonneg hg.le _))

theorem signed {p : ℕ} (hp : 2≤p) (hq : p≤J.order) :
    ∃ D : ℝ, 0<D ∧ ∃ s : ℕ, ∀ᶠ m : ℕ in atTop,
      ∀ (z : LocalFormal.Datum R.family Γ), z.level=m →
      ∀ (Y : Bulk.Chain R.family.path) (F : AnalyticInput J A z) (M : SignedAnalyticOutput caps Y K F),
        let g := regulatorRun R.family z.cutoff z.period (z.level+1)
        |M.plan.predict z.level-(plan M.plan p).predict z.level| * g^2 ≤ D*A.admittedCost m^s*g^(p+1) := by
  obtain ⟨D,hD,s,bill⟩ := cover (Γ:=Γ) R hG hT A K caps hp hq
  refine ⟨D,hD,s,?_⟩
  filter_upwards [bill] with m buy z hz Y F M
  exact buy z hz Y F (FundedPhysicalCatalogue.ofSigned M) (FundedExactKineticContact.tested R M hG _)

end YM.Integration.QLocalKineticOrderRestriction
end
