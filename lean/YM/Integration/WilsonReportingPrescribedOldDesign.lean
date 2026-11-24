import YM.Integration.WilsonReportingPrescribedOldIncome

/-! The loss in perturbative order is selected from the fixed physical MS
prescription before choosing the requested perturbative order of the input
or any of the actual analytic schedules. -/
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldDesign
open Function Filter Finset Lattice Wilson RG Marker Precision Source
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open MergeProof MergeProof.Accent ActualOriginalQCharges ActualOriginalQPackets ActualOriginalQReaders
open OPE.Therm RG05Readout RG05Readout.Native RG05Readout.Flatten
open scoped Topology BigOperators Classical
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {B : MS.Local.Physical.Deck G}
    (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B)
open Pert.Asymptotics IterationFour
open private capped from YM.Integration.WilsonReportingPrescribedOldScale
open private thermal from YM.Integration.WilsonReportingPrescribedOldIncome

private theorem menu (Q : MS.Land.Prescription B) (μ : ℝ) (K : ℕ) :
    ∃ e : ℕ, ∀ (J : Request V) (A : NumericSchedule R.family J), ∃ C : ℝ, 0 < C ∧ ∀ᶠ j : ℕ in atTop, ∀ {m t : ℕ}, j ≤ t →
      WilsonReportHarvestUpperRange.eligible R.family.S m j t →
      ∀ (d : LocalFormal.Datum R.family (Stock.census V)), d.cutoff = t+1 →
      ∀ (o : V → Site (R.family.side (d.level+1) d.period)) (orders : V → ℕ), (∀i,orders i ≤ K) →
      ActualOriginalQInitialInput.normalizer R hG u J A d Q o μ orders ≤ C*(R.family.path.levels.clock.hatBeta j)^e := by
  obtain ⟨c, cp, e, fees⟩ := ActualOriginalFeeGrowth.shifted_bound B Q u K μ
  refine ⟨e,?_⟩
  intro J A
  obtain ⟨a, ap, dates⟩ := WilsonReportingPrescribedOldScale.clock R hG
  let W := max 1 (totalRowPrice (ActualOriginalQPointSetup.pointDatum R J 0 0 (fun _ => 0)) u (fun _ => 1) 1)
  let D := max 1 c * (max 1 a)^e
  have wp : 1 ≤ W := le_max_left _ _
  have dp : 1 ≤ D := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ (le_max_left _ _))
  refine ⟨D*W,mul_pos (zero_lt_one.trans_le dp) (zero_lt_one.trans_le wp),?_⟩
  filter_upwards [dates] with j price
  intro m t jt eligible d cut o orders upper
  let β := R.family.path.levels.clock.hatBeta j
  have bp : 1 ≤ β := (R.family.path.levels.fits.delayed _).le
  have P : 1 ≤ D*β^e := one_le_mul_of_one_le_of_one_le dp (one_le_pow₀ bp)
  have hold : 1+‖R.family.S.scale d.cutoff‖ ≤ (max 1 a)*β := by
    rw [cut]
    exact (price jt eligible).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans bp))
  have charges (s : Slot u) : ‖fee Q u (μ-R.family.S.scale d.cutoff) orders s‖ ≤ D*β^e := by
    calc
      _ ≤ c*(1+‖R.family.S.scale d.cutoff‖)^e := fees s.1 (orders s.1) (upper s.1) s.2 _
      _ ≤ max 1 c*((max 1 a)*β)^e := mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ (by positivity) hold e)
        (by positivity) (zero_le_one.trans (le_max_left _ _))
      _ = _ := by unfold D; rw [mul_pow];ring
  exact (capped R hG u J A d Q o μ orders P charges).trans_eq (by dsimp only [W]; ring)


theorem original (Q : MS.Land.Prescription B) (μ : ℝ) (K : ℕ) :
    ∃ excess : ℕ, ∀ (J : Request V) (A : NumericSchedule R.family J) {ε : ℝ}, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j : ℕ in atTop,
    ∀ {b t : ℕ}, j ≤ t → WilsonReportHarvestUpperRange.eligible R.family.S b j t →
    ∀ (d : LocalFormal.Datum R.family (Stock.census V)), d.cutoff = t+1 →
    ∀ (o : V → Site (R.family.side (d.level+1) d.period)) (orders : V → ℕ), (∀i,orders i ≤ K) →
    ∀ (s : (Stock.census V).Mode) (q : ℝ),
      let h := ActualOriginalQInitialInput.normalizer R hG u J A d Q o μ orders
      let g := regulatorRun R.family d.cutoff d.period (j+1)
      h^s.val.card * (δ*g^(q+excess)) ≤ ε*g^q := by
  obtain ⟨e, schedule⟩ := menu R hG u Q μ K
  let v := Fintype.card V
  let excess := 2*e*v
  refine ⟨excess,?_⟩
  intro J A ε ep
  obtain ⟨c, cp, dates⟩ := schedule J A
  let fare := (c*(2:ℝ)^e)^v
  have positive : 0 < fare := pow_pos (mul_pos cp (by positivity)) _
  refine ⟨ε/fare,div_pos ep positive,?_⟩
  filter_upwards [dates] with j price
  intro b t jt kept d term o orders permitted s q
  let h := ActualOriginalQInitialInput.normalizer R hG u J A d Q o μ orders
  let g := regulatorRun R.family d.cutoff d.period (j+1)
  let β := R.family.path.levels.clock.hatBeta j
  have live : j < d.cutoff := by omega
  have gp : 0 < g := Currency.g_pos R.makes _ _ _ live
  have hp : 1 ≤ h := le_max_left _ _
  have hb : 0 ≤ β := zero_le_one.trans (R.family.path.levels.fits.delayed _).le
  have charge : h*g^(2*e) ≤ c*(2:ℝ)^e := by
    calc _ ≤ (c*β^e)*(g^2)^e := by rw [←pow_mul]; exact mul_le_mul_of_nonneg_right (price jt kept d term o orders permitted) (pow_nonneg gp.le _)
         _ = c*(β*g^2)^e := by rw [mul_pow];ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hb (sq_nonneg _)) (thermal R hG live) _) cp.le
  have cover : s.val.card ≤ v := Finset.card_le_univ _
  have earned : h^s.val.card*g^excess ≤ fare := by
    calc _ ≤ h^v*g^excess := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hp cover) (pow_nonneg gp.le _)
         _ = (h*g^(2*e))^v := by rw [mul_pow,←pow_mul]
         _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (zero_le_one.trans hp) (pow_nonneg gp.le _)) charge _
  change h^s.val.card * (ε/fare*g^(q+(excess:ℝ))) ≤ ε*g^q
  rw [Real.rpow_add gp, Real.rpow_natCast]
  calc _ = ((ε/fare)*(h^s.val.card*g^excess))*g^q := by ring
       _ ≤ ((ε/fare)*fare)*g^q := mul_le_mul_of_nonneg_right
         (mul_le_mul_of_nonneg_left earned (div_pos ep positive).le) (Real.rpow_nonneg gp.le _)
       _ = _ := by rw [div_mul_cancel₀ _ positive.ne']


end YM.Integration.WilsonReportingPrescribedOldDesign
