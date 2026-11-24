import YM.Integration.WilsonReceivedCloseReentry
import YM.Integration.WilsonReceivedCloseChainFunding

/-! Page expenditure at the cohort's first receipt, before the ordinary close descent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseEndpoint
open private currency from YM.Integration.WilsonReceivedCloseInterval
open Filter Finset PhysicalNext.Repeat.Legato Pert.Asymptotics QuadraticLocal QuadraticLocal.Advent
open scoped Topology BigOperators

variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "H" => R.alloy.B.a.clock.hatBeta
local notation "B" => budgetR R

include simple in
theorem original (a : ℕ) {η : ℝ} (loss : 0 < η) :
    ∀ᶠ b : ℕ in atTop, ∀ N per, b ≤ N →
      ((B b)^2*(B (b+1))^7)^a ≤ (regulatorRun R.family N per b)^(-η) := by
  have grows : Tendsto H atTop atTop := RG01.Physical.hats simple R.alloy.B.a
  have next := RG01.Physical.nextHat simple R.alloy.B.a
  have next₂ := (tendsto_add_atTop_nat 1).eventually next
  have head := WilsonMovingMentorPageReserve.powers R simple (2*a) (δ:=η/16) (by positivity)
  have upper := (tendsto_add_atTop_nat 1).eventually
    (WilsonMovingMentorPageReserve.powers R simple (7*a) (δ:=η/16) (by positivity))
  filter_upwards [head,upper,next,next₂,grows.eventually_ge_atTop (4:ℝ)] with b now later first second warm N per top
  let B₀ (j : ℕ) := zero_le_one.trans (budget_pos (i:=j) R)
  have low := now (B b) (B₀ b) (min_le_right ..)
  have hi := later (B (b+1)) (B₀ _) (min_le_right ..)
  have H₀ : 0 ≤ H b := by linarith only [warm]
  have Hp (j : ℕ) : 0 ≤ H j := zero_le_one.trans (R.alloy.B.a.fits.delayed _).le
  have quad : 4*H b ≤ (H b)^2 := by nlinarith only [mul_nonneg H₀ (sub_nonneg.mpr warm)]
  have lowerGrowth : H (b+1) ≤ (H b)^2 := first.trans ((by linarith only [H₀] : 2*H b ≤ 4*H b).trans quad)
  change H ((b+1)+1) ≤ 2*H (b+1) at second
  have upperGrowth : H ((b+1)+1) ≤ (H b)^2 := (by linarith only [first,second] : H ((b+1)+1) ≤ 4*H b).trans quad
  have one := low.trans (Real.rpow_le_rpow (Hp _) lowerGrowth (by positivity))
  have two := hi.trans (Real.rpow_le_rpow (Hp _) upperGrowth (by positivity))
  have measured := (R.makes.wilson.represents N per b top).band.1
  change H b/2 ≤ R.family.path.β N per b at measured
  calc
    _ = (B b)^(2*a)*(B (b+1))^(7*a) := by rw [mul_pow,pow_mul,pow_mul]
    _ ≤ ((H b)^2)^(η/16)*((H b)^2)^(η/16) :=
      mul_le_mul one two (pow_nonneg (B₀ _) _) (Real.rpow_nonneg (sq_nonneg _) _)
    _ = (H b)^(η/4) := by
      rw [←Real.rpow_add (by positivity : 0 < (H b)^2),←Real.rpow_natCast (H b) 2,←Real.rpow_mul H₀]
      congr 1
      push_cast
      ring
    _ ≤ _ := currency warm measured loss

include simple in
theorem with_history (degree a q : ℕ) {cap η ε : ℝ} (cn : 0 ≤ cap) (loss : 0 < η) (en : 0 ≤ ε) :
    ∀ᶠ b : ℕ in atTop, ∀ m ≤ b, PaceR.Close R degree cap m b → ∀ N per, b ≤ N →
      ∀ i, m ≤ i → i ≤ b → ∀ (e : ℝ), 0 ≤ e → (∀ j ∈ Ico i b, 2 ≤ B j) →
      ((B b)^2*(B (b+1))^7)^a*
        ((∏ j ∈ Ico i b,((B j)^2*(B (j+1))^7)^a)*
          (e+∑ j ∈ Ico i b,ε*(regulatorRun R.family N per (min N (j+2)))^q)) ≤
        (regulatorRun R.family N per b)^(-η)*(e+ε*(3*regulatorRun R.family N per b)^q) := by
  have half : 0 < η/2 := by positivity
  filter_upwards [original R simple a half,WilsonReceivedCloseChainFunding.original R simple degree a q cn half en,
    WilsonReceivedCloseChainFunding.upper R simple degree cap] with b launch chain temp m mb close N per top i mi ib e ep issued
  let g := regulatorRun R.family N per b
  have gp : 0 < g := (temp m mb close N per top b mb top).1
  have gap (j:ℕ) : 0 ≤ (B j)^2*(B (j+1))^7 :=
    mul_nonneg (sq_nonneg _) (pow_nonneg (zero_le_one.trans (budget_pos R)) _)
  have rent := chain m mb close N per top i mi ib (fun j => (B j)^2*(B (j+1))^7) (fun _ => a) e ep
    (fun j hj => ⟨issued j hj,gap j,le_rfl,le_rfl⟩)
  have prev := launch N per top
  have j₀ (j) (hj:j ∈ Ico i b) := (temp m mb close N per top (min N (j+2)) (by
    have h := (mem_Ico.mp hj).1
    omega) (min_le_left ..)).1.le
  apply (mul_le_mul prev rent (mul_nonneg (prod_nonneg (fun j _ => pow_nonneg (gap j) _))
    (add_nonneg ep (sum_nonneg (fun j hj => mul_nonneg en (pow_nonneg (j₀ j hj) _))))) (Real.rpow_nonneg gp.le _)).trans
  change g^(-(η/2))*(g^(-(η/2))*_) ≤ g^(-η)*_
  rw [←mul_assoc,←Real.rpow_add gp,show -(η/2)+ -(η/2)= -η by ring]

end YM.Integration.WilsonReceivedCloseEndpoint
