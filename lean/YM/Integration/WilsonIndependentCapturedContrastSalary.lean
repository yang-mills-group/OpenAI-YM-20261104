import YM.Integration.WilsonIndependentCapturedContrast
import YM.Integration.WilsonIndependentFreshFiniteWage

/-! A fully priced signed occupied discrepancy at the capture page
controls the absolute stopped scalar. The starting unit and the subsequent
positive-rank feeds are both retained under the same deposited action. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonIndependentCapturedContrastSalary
open RegulatorIR RegulatorIR.Budget RegulatorIR.Diagram RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Uniform RegulatorIR.Cluster RegulatorIR.Halo RegulatorIR.Taping RegulatorIR.Spatial
open WilsonIndependentFreshFiniteWage
open Lattice RG
open scoped ENNReal
variable {G : Gauge} {W : Type} {M : W → ℕ} {n : Page M → Side}
variable (S : Heir n G) (T : S.Accounts) {p k u m h a e : ℕ} {L : Meter W}
variable (H : Milieu S T k p L) (R : T.Report m) (Y : T.Report h) (E : T.Report a)
variable {γ : ℝ} {c : Flap M → ℝ≥0∞} {x : W → Room}

include H in
theorem original (window : S.Softness u L c (S.softnessWeight γ) 1) (hu : u ≤ k)
    (old : ∀ w, Bill (R.main (Page.opening M w)) p) (issued : ∀ w, Bill (Y.main (Page.opening M w)) p)
    (joined : ∀ w i, i ≤ p → R.main (Page.opening M w) i - Y.main (Page.opening M w) i =
      E.main (Page.opening M w) i)
    (ward : ∀ f i, i ≤ p → (S.sight f).Way (E.main f.prev) i)
    (gross : W → ℝ) (nonneg : ∀ w, 0 ≤ gross w)
    (income : ∀ i, i ≤ p → ∀ r, Claim L (fun w => S.coverQ x u (Page.opening M w))
      (fun w => ENNReal.ofReal (gross w)) (fun w => E.main (Page.opening M w) i r))
    (stop : Choice M) (he : e ≤ p) : ∃ K : ℝ, ∃ l : ℕ, 0 ≤ K ∧ ∀ w,
      ‖note (R.main (stop.choose w) e 0) - note (Y.main (stop.choose w) e 0)‖ ≤
        K*(L.val w).toReal^l*gross w := by
  let start : Choice M := ⟨fun _ => 0, fun _ => Nat.zero_le _⟩
  let fee := fun w => ENNReal.ofReal (gross w)
  let pay := purse S γ fee
  have opening (w : W) : ticket (S.softnessWeight γ) pay (start.choose w) = fee w := by
    rw [value S γ fee]
    change fee w * ENNReal.ofReal ((S.l (Page.opening M w) / S.l (Page.opening M w))^γ) = _
    rw [div_self (S.hl _).ne',Real.one_rpow,ENNReal.ofReal_one,mul_one]
  have bend : S.Bend T E u p start x (S.softnessWeight γ) pay 1 L := by
    refine ⟨?_,ward,fun _ _ _ _ _ lo => False.elim (by omega),fun _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
    intro i hi r _
    simp only [opening]
    exact income i hi r
  have drift := S.woven T E H.core H.sky window bend hu (j:=stop) (fun _ => Nat.zero_le _) he
  simp only [opening] at drift
  have initial := income e he 0
  change Carry L fee (fun w => Budget.Packet.markQ (S.coverQ x u (Page.opening M w)) (E.main _ e 0)) at initial
  simp only [quotaNote] at initial
  apply RegulatorIR.Centered.Carry_rt nonneg
  apply Carry.mono (Carry.add drift initial)
  intro w
  have hh := WilsonIndependentCapturedContrast.balance S T H R Y E old issued joined (stop.choose w) e he
  have eq := congrArg (fun A => note (A 0)) hh
  change note (R.main (stop.choose w) e 0) - note (Y.main (stop.choose w) e 0) =
    note (E.main (stop.choose w) e 0) at eq
  change ‖note (R.main (stop.choose w) e 0) - note (Y.main (stop.choose w) e 0)‖ₑ ≤ _
  rw [eq]
  change ‖note (E.main (stop.choose w) e 0)‖ₑ ≤
    ‖note (E.main (stop.choose w) e 0)-note (E.main (Page.opening M w) e 0)‖ₑ +
      ‖note (E.main (Page.opening M w) e 0)‖ₑ
  exact (enorm_add_le (note (E.main (stop.choose w) e 0) - note (E.main (Page.opening M w) e 0))
    (note (E.main (Page.opening M w) e 0))) |> fun bound => by simpa only [sub_add_cancel] using bound

end YM.Integration.WilsonIndependentCapturedContrastSalary
