import YM.Integration.WilsonReceivedCloseCash
import YM.Integration.WilsonRootedKioskCloseWalk

/-! Accumulate inherited fees between the original physical capture and
reporting dates at their measured coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedClosePrices
open Filter Lattice Wilson RG RG16 QuadraticLocal.Advent
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Classical BigOperators Topology

variable {G : Gauge} (R : Run G) (simple : G.Simple)

private theorem telescope (a b : ℕ) (ledger : ℕ → ℝ) (u : ℝ) {m : ℕ} (start : m ≤ b)
    (paid : ∀ i, m ≤ i → i < b → ledger i+u ≤ (budgetR R i)^(a+2)*(ledger (i+1)+u)) :
    ledger m+u ≤ (PaceR.roof R m b)^(a+2)*(ledger b+u) := by
  induction start using Nat.decreasingInduction with
  | self => simp [PaceR.roof]
  | of_succ i ib ih =>
    have here := paid i le_rfl ib
    have next := ih (fun j lo hi=> paid j (le_trans (Nat.le_succ _) lo) hi)
    rw [PaceR.roof_step R ib,mul_pow,mul_assoc]
    exact here.trans (mul_le_mul_of_nonneg_left next (pow_nonneg (zero_le_one.trans (budget_pos R)) _))

/-- Every dated input is the shifted fee issued by `WilsonReceivedCloseCash.enrolled`.
The same allowed truncation amount pays each date once inside the roof. -/
def Incomes {N per : ℕ} (a p : ℕ) (ε : ℝ) (m b : ℕ) (ledger : ℕ → ℝ) : Prop :=
  ∀ i, m ≤ i → i < b → ∀ u, ε*(regulatorRun R.family N per (i+1))^p ≤ u →
    ledger i+u ≤ (budgetR R i)^(a+2)*(ledger (i+1)+u)

include simple in
theorem original (degree a p : ℕ) {Q η ε : ℝ} (cap : 0 ≤ Q) (loss : 0 < η) (cost : 0 ≤ ε) :
    ∀ᶠ b:ℕ in atTop, ∀ m ≤ b, PaceR.Close R degree Q m b → ∀ N per : ℕ, b≤N →
      ∀ ledger : ℕ → ℝ, 0 ≤ ledger b → Incomes R (N:=N) (per:=per) a p ε m b ledger →
      ledger m ≤ (regulatorRun R.family N per b)^(-η)*
          (ledger b+ε*(3*regulatorRun R.family N per b)^p) := by
  filter_upwards [WilsonReceivedCloseInterval.purchased R simple degree a cap loss]
    with b roof m mb close N per top ledger bound issued
  obtain ⟨span, temperatures⟩ := roof m mb close N per top
  let u := ε*(3*regulatorRun R.family N per b)^p
  have up : 0 ≤ u := mul_nonneg cost (pow_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr (Real.sqrt_nonneg _))) _)
  have paid i lo hi := issued i lo hi u (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) (temperatures (i+1) (by omega) (by omega)) p) cost)
  exact (le_add_of_nonneg_right up).trans ((telescope R a b ledger u mb paid).trans
    (mul_le_mul_of_nonneg_right (span m le_rfl mb) (add_nonneg bound up)))

include simple in
/-- The dated income on the actual moving pair of mesh levels. The radius is
chosen before the UV cutoff and physical period. -/
theorem at_capture (slow : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (wide : 0 < B)
    (a p : ℕ) {η ε : ℝ} (loss : 0 < η) (cost : 0 ≤ ε) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r, 0 < r → r ≤ r₀ →
      let m := WilsonCloseCaptureDate.level R.family.S r
      let b := WilsonMeasuredWindow.stop R.family.path.levels simple B r
      ∀ N per : ℕ, b≤N → ∀ ledger : ℕ → ℝ, 0 ≤ ledger b →
        Incomes R (N:=N) (per:=per) a p ε m b ledger →
        ledger m ≤ (regulatorRun R.family N per b)^(-η)*
          (ledger b+ε*(3*regulatorRun R.family N per b)^p) := by
  obtain ⟨K, stages⟩ := Filter.eventually_atTop.mp
    (original R simple 1 a p (Q:=((B+2:ℕ):ℝ)) (by positivity) loss cost)
  refine ⟨R.family.S.a K,R.family.S.a_pos K,?_⟩
  intro r positive below m b
  have win := WilsonCloseCaptureDate.window R slow simple wide positive
    (below.trans (R.family.S.strictAnti.antitone (Nat.zero_le _)))
  have early : K ≤ m := by
    by_contra! later
    exact (not_lt_of_ge (below.trans (R.family.S.strictAnti.antitone (show m+1≤K by omega)))) win.2.1
  have close : PaceR.Close R 1 ((B+2:ℕ):ℝ) m b := by
    unfold PaceR.Close
    rw [pow_one]
    exact win.2.2.2.2.2
  exact stages b (early.trans win.1.le) m win.1.le close

end YM.Integration.WilsonReceivedClosePrices
