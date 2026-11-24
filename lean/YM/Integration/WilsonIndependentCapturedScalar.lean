import YM.RegulatorIR.Ledger.Turn
import YM.RegulatorIR.Ledger.Hue
import YM.RegulatorIR.Centered.Breadth
import YM.FVAAlt2.Rocket.Orbit

/-! Infrared scalar drift of a captured marked field on its original dated
Wick report. Its positive-rank wage is measured at capture. The angular
vacuum and all earlier scalar feeds remain those of the same report. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentCapturedScalar
open RegulatorIR RegulatorIR.Budget RegulatorIR.Spatial RegulatorIR.Budget.Packet
open RegulatorIR.Uniform RegulatorIR.Ledger
open RegulatorIR.Ledger.Sky
open scoped ENNReal Classical
variable {W : Type} {M : W → ℕ} {X Y : Page M → Type}
variable (S : Sky X Y) (T : S.Accounts) {m : ℕ} (Z : T.Report m)
variable {p u b e : ℕ} {L : Meter W} {x : W → Room} {c : Flap M → ℝ≥0∞}
variable {base capture stop : Choice M} {γ : ℝ}

/-- Put the actual wage at the capture mesh even when the mesh used by the
underlying report is normalized at a much earlier birth. -/
private theorem currency (k : Choice M) (gross : W → ℝ) (t : Choice M) (w : W) :
    ticket (S.softnessWeight γ) (fun v => ENNReal.ofReal (gross v * S.l (k.choose v)^γ))
      (t.choose w) = ENNReal.ofReal (gross w * (S.l (k.choose w) / S.l (t.choose w))^γ) := by
  change ENNReal.ofReal (gross w * S.l (k.choose w)^γ) *
    (ENNReal.ofReal (S.l (t.choose w)^γ))⁻¹ = _
  rw [← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos (S.hl _) _),
    Real.div_rpow (S.hl _).le (S.hl _).le, mul_div_assoc]

/-- Bound the entire scalar feed from a weak stop to the actual last page.
Only nonconstant ranks at the capture date enter the starting wage. -/
theorem drift (B : S.Primitive L p b) (N : S.Supplies T L p b)
    (light : S.Radiants L γ u 1 c base) (hu : u ≤ b)
    (gross : W → ℝ) (hg : ∀ w, 0 ≤ gross w)
    (wage : ∀ i, i ≤ p → ∀ r, 0 < r →
      Claim L (fun w => S.coverQ x u (capture.choose w)) (fun w => ENNReal.ofReal (gross w))
        (fun w => Z.main (capture.choose w) i r))
    (ward : ∀ a i, i ≤ p → (S.sight a).Way (Z.main a.prev) i)
    (order : capture.age ≤ stop.age) (he : e ≤ p) :
    ∃ C : ℝ, ∃ d : ℕ, 0 ≤ C ∧ ∀ w,
      ‖note (Z.main (Page.finallyW M w) e 0) - note (Z.main (stop.choose w) e 0)‖ ≤
      C * (L.val w).toReal^d * (gross w * (S.l (capture.choose w) / S.l (stop.choose w))^γ) := by
  let s (w : W) := ENNReal.ofReal (gross w * S.l (capture.choose w)^γ)
  have row : S.Bend T Z u p capture x (S.softnessWeight γ) s 1 L := by
    refine ⟨?_, ward, fun _ _ _ _ _ hlt => False.elim (by omega), fun _ => ENNReal.ofReal_ne_top⟩
    intro i hi r hr
    have paid := wage i hi r hr
    convert paid using 1
    funext w
    rw [show ticket (S.softnessWeight γ) s (capture.choose w) = _ from currency S capture gross capture w,
      div_self (S.hl _).ne', Real.one_rpow, mul_one]
  have tail := S.marled T Z B N (S.warmer light) row hu order he
  have exactCurrency : (fun w => ticket (S.softnessWeight γ) s (stop.choose w)) =
        (fun w => ENNReal.ofReal (gross w * (S.l (capture.choose w) / S.l (stop.choose w))^γ)) :=
    funext fun w => currency S capture gross stop w
  rw [exactCurrency] at tail
  exact RegulatorIR.Centered.Carry_rt (fun w => mul_nonneg (hg w)
    (Real.rpow_nonneg (div_nonneg (S.hl _).le (S.hl _).le) _)) tail

end YM.Integration.WilsonIndependentCapturedScalar

