import YM.Integration.WilsonReporterWeightedIncome
import YM.Integration.WilsonReporterWeightedElection
import YM.Integration.WilsonReporterWeightedDeployment

/-! The enlarged doses use the actual numerator and true occupied-source salary
of the measured finite stamp. The posting precision and reserve precede the date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReporterWeightedCash
open Next.Rank Next.Rank.Tapes Next.Rank.Tapes.West MergeProof MergeProof.Accent
open Filter Function Lattice Wilson RG Marker Spindle Rise Ribbon Perch Station Atlas
     Vac.Numbers Source Extra.Histories PhysicalNext.Repeat.Legato.Bandage
open scoped BigOperators Classical Topology

variable {G : Gauge} (C : Family G) {W : Bid.Worth} {u ψ φ δ : ℕ → ℝ} {r : ℕ → ℕ}
    {door : ∀ N p m : ℕ, m < N → GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
local notation "AX" => C.path.levels

theorem original (h : G.Simple) (H : C.Makes) (scrim : Scrim C W u ψ φ δ (fly AX) r door)
    {n D : ℕ} (θ : ℕ) (e z : ℝ) (d : Fin n → ℕ) (g : (i : Fin n) → C.label (d i))
    (grades : ∀ i, d i≤D) (tariff : ∀ i, generator G (d i) ≤ z) :
    ∀ᶠ k : ℕ in atTop, ∀ (α : Purse) (b reserve : ℝ) (_ : 0≤b) (add : Fin n → ℝ),
    α.f=e → α.taylor=θ → b*D+D+2+reserve ≤ α.credit → (∀ i, add i ≤ reserve) →
    year C α.taylor k → ∀ N p, k≤N → ∀ {Q q X}
      (T : (i : Fin n)→ StampDuty C k N p (d i) α.taylor Q q X)
      (t : (i : Fin n)→ C.label (d i)),
    (∀ i, Price.Solves C (mag AX b k) (d i) k N p (T i).T (g i) (t i)) →
    let s := clim AX k
    let a := fun i : Fin n => (Perch.bill (add i) s : ℂ)
    let row := fun i : Fin n => a i • t i
    (∀ i, Price.Solves C (mag AX b k) (d i) k N p (T i).T (a i • g i) (row i)) ∧
      (∀ i, α.cash s*moneys C (d i) k N p (row i) ≤ Perch.bill (-8) s) ∧
      (∀ i, Rise.coin ((T i).W (row i)) ≤ α.principal s) ∧
      (∀ i, Hat s^z * paid C (d i) k N p (row i) ≤ fly AX (d i) k) := by
  filter_upwards [eventually_all.mpr (fun i=>WilsonReporterWeightedIncome.original C h H scrim (d i) θ (g i)),
    eventually_all.mpr (fun i => (hat_rate AX h).eventually (tremor e (tariff i)))] with k earn hard
  intro α b reserve hb add he ht hc ar stage N p higher Q q X T t fitted s a row
  subst θ
  have credit (i : Fin n) : add i+(b*d i+saves C (d i))≤α.credit := by
    have gD : (d i : ℝ) ≤ D := Nat.cast_le.mpr (grades i)
    linarith only [hc, ar i, Tapes.savings C (d i), gD, mul_le_mul_of_nonneg_left gD hb]
  have wages (i : Fin n) : Price.Solves C (mag AX b k) (d i) k N p (T i).T (a i • g i) (row i) ∧
      bill e s*moneys C (d i) k N p (row i) ≤ bill (-8) s ∧
      Rise.coin ((T i).W (row i)) ≤ bill (add i+(b*d i+saves C (d i))) s := by
    exact earn i b e (add i) hb (by linarith only [α.fits,he,credit i]) stage N p higher (T i) _ (fitted i)
  refine ⟨fun i=>(wages i).1,fun i=>?_,fun i=>?_,fun i=>?_⟩
  · unfold Purse.cash; rw [he]; exact (wages i).2.1
  · exact (wages i).2.2.trans (Glimmer.billed _ (credit i))
  · have pos : 0≤Hat s^z := (Real.rpow_pos_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr
        (zero_lt_one.trans (C.path.levels.fits.delayed _)))) z).le
    exact (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Spindle.paid_pos ..)
      (C.path.levels.params k).columns_ge) pos).trans (hard i _ (Spindle.money_nn ..) (wages i).2.1)

end YM.Integration.WilsonReporterWeightedCash
