import YM.Integration.WilsonReceivedCloseForcedPrice
import YM.Integration.WilsonMovingMentorPageReserve

/-! Radius restoration on an original close interval. A persisting old mark
uses both adjacent genuine stage budgets once. New births have their own
single entrance radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseReentry
open private currency from YM.Integration.WilsonReceivedCloseInterval
open Filter Finset Lattice Wilson RG QuadraticLocal.Advent
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Classical BigOperators Topology

/-- The two-date re-inscription bound at its original tolerance one. -/
theorem one {previous next h bill spent rent g : ℝ} (p : ℕ)
    (was : 4 ≤ previous) (now : 2 ≤ next) (held : rent ≤ 1)
    (gp : 0 ≤ g) (gc : g ≤ 1) (job : bill ≤ 8*previous*rent+g^p)
    (paid : h ≤ max (max 1 bill) (previous^5+1)) (fit : spent ≤ 1) :
    h ≤ previous^6 ∧ h*(2*max 1 (next*spent)) ≤ next^2*previous^6 := by
  have prev1 : 1 ≤ previous := by linarith
  have next1 : 1 ≤ next := by linarith
  have fee : bill ≤ previous^3 := by
    have upper := mul_le_mul_of_nonneg_left held (show (0:ℝ) ≤ 8*previous by positivity)
    rw [mul_one] at upper
    have sq : 9 ≤ previous^2 := by nlinarith only [was,sq_nonneg (previous-4)]
    calc
      _ ≤ 8*previous+1 := job.trans (add_le_add upper (pow_le_one₀ gp gc))
      _ ≤ previous*9 := by linarith
      _ ≤ previous*previous^2 := mul_le_mul_of_nonneg_left sq (by linarith)
      _ = _ := by ring
  have sub : previous^5+1 ≤ previous^6 := by
    calc
      _ ≤ previous^5*2 := by linarith only [one_le_pow₀ (n:=5) prev1]
      _ ≤ previous^5*previous := mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (by linarith) _)
      _ = _ := by ring
  have full := paid.trans (max_le (max_le (one_le_pow₀ prev1)
    (fee.trans (pow_le_pow_right₀ prev1 (by decide : 3≤6)))) sub)
  refine ⟨full,?_⟩
  have n0 : 0 ≤ next := by linarith
  have room : max 1 (next*spent) ≤ next := max_le next1 (by simpa using mul_le_mul_of_nonneg_left fit n0)
  have scaled : 2*max 1 (next*spent) ≤ next^2 := by
    calc
      _ ≤ 2*next := mul_le_mul_of_nonneg_left room (by norm_num)
      _ ≤ next*next := mul_le_mul_of_nonneg_right now n0
      _ = _ := by ring
  rw [mul_comm (next^2)]
  exact mul_le_mul full scaled (by linarith only [le_max_left (1:ℝ) (next*spent)]) (pow_nonneg (by linarith) _)

/-- The exact old-label inverse ratio on the join used for the ensuing
SuccessStory, including both factors of its actual shrinking wallet. -/
theorem retained {old joined h next spent : ℝ} (hp : 1 ≤ h)
    (actual : joined=old / max 1 (next*spent) / 2) :
    old=(h*(2*max 1 (next*spent)))*(joined/h) := by
  have h0 : h≠0 := by linarith
  have m0 : max 1 (next*spent) ≠ 0 := (zero_lt_one.trans_le (le_max_left ..)).ne'
  rw [actual]
  field_simp

variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "B" => budgetR R
local notation "H" => R.alloy.B.a.clock.hatBeta

include simple in
theorem small (degree : ℕ) (Q : ℝ) :
    ∀ᶠ b : ℕ in atTop, ∀ m ≤ b, PaceR.Close R degree Q m b →
      ∀ N per i, m ≤ i → i ≤ N → regulatorRun R.family N per i ≤ 1 := by
  have grows : Tendsto H atTop atTop :=
    tendsto_const_nhds.add_atTop (R.alloy.B.a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [PaceR.covers_hat R simple degree Q,grows.eventually_ge_atTop (8:ℝ)]
    with b temp warm m mb close N per i mi iN
  have half := temp m m le_rfl mb close
  have rising := WilsonStartup.Timing.hat_mono R.alloy.B.a (Gauge.slopeConstant_pos simple).le mi
  have band := (R.makes.wilson.represents N per i iN).band.1
  change H i/2 ≤ R.family.path.β N per i at band
  apply inv_le_one_of_one_le₀
  apply (Real.le_sqrt zero_le_one (by linarith only [warm,half,rising,band])).mpr
  linarith only [warm,half,rising,band]

private theorem adjacent (a : ℕ) {m b : ℕ} (head : m ≤ b) :
    (∏ i ∈ Ico m b, (B i)^(2*a)*(B (i+1))^(7*a))*(B m)^(7*a) =
      (PaceR.roof R m b)^(9*a)*(B b)^(7*a) := by
  induction head using Nat.decreasingInduction with
  | self => simp [PaceR.roof]
  | of_succ i ib ih =>
    rw [← insert_Ico_add_one_left_eq_Ico ib, prod_insert (by simp), PaceR.roof_step R ib, mul_pow]
    calc
      _ = (B i)^(9*a)*((∏ j ∈ Ico (i+1) b, (B j)^(2*a)*(B (j+1))^(7*a))*(B (i+1))^(7*a)) := by
        rw [show 9*a=2*a+7*a by omega,pow_add]
        ring
      _ = _ := by rw [ih]; ring

include simple in
/-- The funded neighbouring budgets for every suffix, with one spare roof for summing the fresh errors. -/
theorem envelope (degree a : ℕ) {Q η : ℝ} (cap : 0 ≤ Q) (loss : 0 < η) :
    ∀ᶠ b : ℕ in atTop, ∀ m ≤ b, PaceR.Close R degree Q m b → ∀ N per : ℕ, b ≤ N →
      ∀ i, m ≤ i → i ≤ b →
        (∏ j ∈ Ico i b, (B j)^(2*a)*(B (j+1))^(7*a))*(PaceR.roof R i b) ≤
          (regulatorRun R.family N per b)^(-η) := by
  have grows : Tendsto H atTop atTop :=
    tendsto_const_nhds.add_atTop (R.alloy.B.a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [WilsonReceivedCloseInterval.purchased R simple degree (9*a) cap (η:=η/2) (by positivity),
    WilsonMovingMentorPageReserve.powers R simple (7*a) (δ:=η/16) (by positivity),
    RG01.Physical.nextHat simple R.alloy.B.a,grows.eventually_ge_atTop (36:ℝ)]
      with b span finalFee next warm m mb close N per top i mi ib
  let x := regulatorRun R.family N per b
  have lower := (R.makes.wilson.represents N per b top).band.1
  change H b/2 ≤ R.family.path.β N per b at lower
  have x0 : 0 < x := inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  have room := (span m mb close N per top).1
  have B0 (i:ℕ) : 0 ≤ B i := zero_le_one.trans (budget_pos R)
  have endpoint : (B b)^(7*a) ≤ x^(-(η/2)) := by
    have atb := finalFee (B b) (B0 b) (min_le_right ..)
    have even : H (b+1) ≤ (H b)^2 := next.trans (by nlinarith only [warm,sq_nonneg (H b-18)])
    calc
      _ ≤ (H (b+1))^(η/16) := atb
      _ ≤ ((H b)^2)^(η/16) := Real.rpow_le_rpow (zero_le_one.trans (R.alloy.B.a.fits.delayed _).le) even (by positivity)
      _ = (H b)^((η/2)/4) := by
        rw [← Real.rpow_natCast (H b) 2,← Real.rpow_mul (by linarith : 0 ≤ H b)]
        congr 1
        push_cast
        ring
      _ ≤ _ := currency (by linarith) lower (by positivity)
  have roof : (PaceR.roof R i b)^(9*a+1) ≤ x^(-(η/2)) :=
    (pow_le_pow_right₀ (PaceR.roof_ge ..) (by omega : 9*a+1 ≤ 9*a+2)).trans (room i mi ib)
  let P := ∏ j ∈ Ico i b, (B j)^(2*a)*(B (j+1))^(7*a)
  have P₀ : 0 ≤ P := prod_nonneg (fun _ _ => mul_nonneg (pow_nonneg (B0 _) _) (pow_nonneg (B0 _) _))
  calc
    _ ≤ (P*(B i)^(7*a))*(PaceR.roof R i b) :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right P₀ (one_le_pow₀ (budget_pos R)))
        (zero_le_one.trans (PaceR.roof_ge ..))
    _ = (PaceR.roof R i b)^(9*a+1)*(B b)^(7*a) := by
      rw [show P*(B i)^(7*a) = _ from adjacent R a ib, pow_succ]; ring
    _ ≤ x^(-(η/2))*x^(-(η/2)) := mul_le_mul roof endpoint (pow_nonneg (B0 _) _) (Real.rpow_nonneg x0.le _)
    _ = _ := by rw [←Real.rpow_add x0]; congr 1; ring

include simple in
theorem original (degree a p : ℕ) {Q η : ℝ} (cap : 0 ≤ Q) (loss : 0 < η) :
    ∀ᶠ b : ℕ in atTop, ∀ m ≤ b, PaceR.Close R degree Q m b → ∀ N per : ℕ, b ≤ N →
      ∀ (aᵢ : ℕ → ℕ) (Ω bill h spent rent : ℕ → ℝ),
        (∀ i, m ≤ i → i ≤ b → 4 ≤ Ω i ∧ Ω i ≤ B i) →
        (∀ i, m ≤ i → i < b →
          aᵢ i ≤ a ∧ rent i ≤ 1 ∧ spent i ≤ B (i+1) ∧ 1 ≤ h i ∧
          bill i ≤ 8*Ω (i+1)*rent i+(regulatorRun R.family N per (min N (i+2)))^p ∧
          h i ≤ max (max 1 (bill i)) ((Ω (i+1))^5+1)) →
        (∏ i ∈ Ico m b, (h i*(2*max 1 ((B i)*spent i)))^(aᵢ i)) ≤
          (regulatorRun R.family N per b)^(-η) := by
  filter_upwards [envelope R simple degree a cap loss,small R simple degree Q]
    with b wealth tiny m mb close N per top aᵢ Ω bill h spent rent books posts
  have B0 (i:ℕ) : 0 ≤ B i := zero_le_one.trans (budget_pos R)
  have stop i (v : i ∈ Ico m b) :
      (h i*(2*max 1 (B i*spent i)))^(aᵢ i) ≤ (B i)^(2*a)*(B (i+1))^(7*a) := by
    obtain ⟨mi, ib⟩ := mem_Ico.mp v
    obtain ⟨arity, unit, space, held, rate, keep⟩ := posts i mi ib
    have upper := books (i+1) (by omega) (by omega)
    have lower := books i mi ib.le
    have oldCap := (one (spent:=0) p upper.1 (show 2 ≤ B i by linarith only [lower.1,lower.2])
      unit (inv_nonneg.mpr (Real.sqrt_nonneg _)) (tiny m mb close N per (min N (i+2))
        (by omega) (min_le_left ..)) rate keep zero_le_one).1
    have final : h i ≤ (B (i+1))^6 :=
      oldCap.trans (pow_le_pow_left₀ (by linarith only [upper.1]) upper.2 _)
    have rebate : max 1 (B i*spent i) ≤ B i*B (i+1) :=
      max_le (one_le_mul_of_one_le_of_one_le (budget_pos R) (budget_pos R))
        (mul_le_mul_of_nonneg_left space (B0 i))
    have payment : h i*(2*max 1 (B i*spent i)) ≤ (B i)^2*(B (i+1))^7 := by
      calc
        _ ≤ (B (i+1))^6*((B i)*(B i*B (i+1))) := mul_le_mul final (mul_le_mul
          (by linarith only [lower.1,lower.2]) rebate (zero_le_one.trans (le_max_left ..)) (B0 _))
          (mul_nonneg (by norm_num) (zero_le_one.trans (le_max_left ..))) (pow_nonneg (B0 _) _)
        _ = _ := by ring
    have pos : 0 ≤ h i*(2*max 1 (B i*spent i)) := mul_nonneg (zero_le_one.trans held)
      (mul_nonneg (by norm_num) (zero_le_one.trans (le_max_left ..)))
    rw [pow_mul,pow_mul,←mul_pow]
    exact (pow_le_pow_left₀ pos payment _).trans (pow_le_pow_right₀
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (budget_pos R)) (one_le_pow₀ (budget_pos R))) arity)
  calc
    _ ≤ ∏ i ∈ Ico m b, (B i)^(2*a)*(B (i+1))^(7*a) :=
      prod_le_prod (fun i hi=>pow_nonneg (mul_nonneg (zero_le_one.trans (posts i (mem_Ico.mp hi).1 (mem_Ico.mp hi).2).2.2.2.1)
        (mul_nonneg (by norm_num) (zero_le_one.trans (le_max_left ..)))) _) stop
    _ ≤ _*(PaceR.roof R m b) := le_mul_of_one_le_right
      (prod_nonneg (fun _ _ => mul_nonneg (pow_nonneg (B0 _) _) (pow_nonneg (B0 _) _))) (PaceR.roof_ge ..)
    _ ≤ _ := wealth m mb close N per top m le_rfl mb

end YM.Integration.WilsonReceivedCloseReentry
