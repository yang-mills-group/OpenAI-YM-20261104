import YM.Integration.WilsonReportingPrescribedOldScale

/-! A fixed number of measured coupling powers restores the full original
independent point input, including all its compulsory finite MS counterterms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldIncome
open Filter Lattice Wilson RG Source Marker Precision Pert.Asymptotics IterationFour
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open MergeProof MergeProof.Accent
open scoped Topology Classical
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {B : MS.Local.Physical.Deck G}
  (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B) (J : Request V) (A : NumericSchedule R.family J)

include hG in
private theorem thermal {j N per : ℕ} (live : j < N) :
    R.family.path.levels.clock.hatBeta j*(regulatorRun R.family N per (j+1))^2 ≤ 2 := by
  let L := R.family.path.levels
  let β := (R.family.path.rep N per (j+1)).beta
  have fee := (R.makes.wilson.represents N per (j+1) live).band.1
  have base : 1 ≤ ((L.S.block j).val : ℝ) := by exact_mod_cast (L.S.block j).property
  have step : L.clock.hatBeta j ≤ L.clock.hatBeta (j+1) := by
    unfold Calendar.hatBeta
    rw [Schedule.scale_succ]
    nlinarith only [mul_nonneg (Gauge.slopeConstant_pos hG).le (Real.log_nonneg base)]
  have positive : 0 < β := (div_pos (zero_lt_one.trans (L.fits.delayed _)) (by norm_num)).trans_le fee
  change L.clock.hatBeta j * (Real.sqrt β)⁻¹^2 ≤ _
  rw [inv_pow, ←div_eq_mul_inv, div_le_iff₀ (pow_pos (Real.sqrt_pos.2 positive) 2), Real.sq_sqrt positive.le]
  change L.clock.hatBeta (j+1)/2 ≤ β at fee
  linarith only [step,fee]

/-- `excess` is chosen before the accuracy, the actual reporting and birth
dates, and every original position. The exponent being retained can be real. -/
theorem original (Q : MS.Land.Prescription B) (μ : ℝ) (K : ℕ) :
    ∃ excess : ℕ, ∀ {ε : ℝ}, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j : ℕ in atTop,
    ∀ {b t : ℕ}, j ≤ t → WilsonReportHarvestUpperRange.eligible R.family.S b j t →
    ∀ (d : LocalFormal.Datum R.family (Stock.census V)), d.cutoff = t+1 →
    ∀ (o : V → Site (R.family.side (d.level+1) d.period)) (orders : V → ℕ), (∀i,orders i ≤ K) →
    ∀ (s : (Stock.census V).Mode) (q : ℝ),
      let h := ActualOriginalQInitialInput.normalizer R hG u J A d Q o μ orders
      let g := regulatorRun R.family d.cutoff d.period (j+1)
      h^s.val.card * (δ*g^(q+excess)) ≤ ε*g^q := by
  obtain ⟨c,cp,e,dates⟩ := WilsonReportingPrescribedOldScale.original R hG u J A Q μ K
  let v := Fintype.card V
  let excess := 2*e*v
  let fare := (c*(2:ℝ)^e)^v
  have positive : 0 < fare := pow_pos (mul_pos cp (by positivity)) _
  refine ⟨excess,?_⟩
  intro ε ep
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

end YM.Integration.WilsonReportingPrescribedOldIncome
