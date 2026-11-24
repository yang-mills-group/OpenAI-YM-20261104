import YM.Integration.WilsonPositionProgramTrialTorusBoxes

/-! Arbitrary coordinate strings for the actual finite-period inverse. All
volume dependence stays in the incoming scalar integral of the squared field. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialTorusDifferences
open Finset Lattice Pert.Orb
open WilsonPositionProgramTrialTorusInterior (stock)
open WilsonPositionProgramTrialTorusBoxes (ball)
open scoped Classical BigOperators
variable {n : Side}

def jet : List Axis → (Site n → ℝ) → Site n → ℝ
  | [],u => u
  | i::L,u => ahead i (jet L u)

theorem commute (i : Axis) (u : Site n → ℝ) : lap (ahead i u) = ahead i (lap u) := by
  funext x
  dsimp only [lap,ahead]
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  rw [show x+step j+step i=x+step i+step j by abel,
      show x-step j+step i=x+step i-step j by abel]
  simp only [two_smul]
  ring

theorem harmonic_jet (L : List Axis) (u : Site n → ℝ) : lap (jet L u)=jet L (lap u) := by
  induction L with
  | nil => rfl
  | cons i L ih => exact (commute i _).trans (congrArg (ahead i) ih)

theorem localized (L : List Axis) (a : Site n) (u : Site n → ℝ) :
    ∀ (r : ℝ), (∀ x : Site n, (separation x a : ℝ) ≤ r+L.length → u x=0) →
    ∀ x : Site n, (separation x a : ℝ) ≤ r → jet L u x=0 := by
  induction L with
  | nil =>
    intro r zero x hx
    exact zero x (by simpa using hx)
  | cons i L ih =>
    intro r zero x hx
    have small : ∀ y : Site n, (separation y a : ℝ) ≤ r+1+L.length → u y = 0 := by
      intro y hy
      apply zero
      simp only [List.length_cons,Nat.cast_add_one]
      linarith
    have near := (abs_le.mp (WilsonPositionProgramTrialTorusBoxes.near a x i)).2
    exact sub_eq_zero.mpr ((ih (r+1) small _ (by linarith)).trans (ih (r+1) small _ (by linarith)).symm)

theorem original (L : List Axis) (a : Site n) (u : Site n → ℝ) {w : ℝ} (wp : 0<w) :
    ∀ (r : ℝ), (∀ x : Site n, (separation x a : ℝ) ≤ r+(w+3)*L.length → lap u x=0) →
    stock (ball a r) (jet L u) ≤ (4*(1/w)^2)^L.length*stock (ball a (r+(w+2)*L.length)) u := by
  induction L with
  | nil => intro r _; simp [jet]
  | cons i L ih =>
    intro r h
    simp only [List.length_cons,Nat.cast_add_one] at h ⊢
    have reserve : ∀ x : Site n, (separation x a : ℝ) ≤ r+w+2+(w+3)*L.length → lap u x=0 := by
      intro x hx
      apply h
      linarith
    have valid : ∀ x ∈ ball a (r+w+2), lap (jet L u) x=0 := by
      intro x hx
      rw [harmonic_jet]
      apply localized L a (lap u) (r+w+2) _ x (mem_filter.mp hx).2
      intro y hy
      apply reserve
      have ln : 0 ≤ (L.length : ℝ) := by positivity
      nlinarith only [hy,mul_nonneg wp.le ln,ln]
    have first:=WilsonPositionProgramTrialTorusBoxes.original (jet L u) a r wp valid i
    have later:=mul_le_mul_of_nonneg_left (ih (r+w+2) reserve) (show 0≤4*(1/w)^2 by positivity)
    calc
      _ ≤ _ := first.trans later
      _ = _ := by
        rw [show r+w+2+(w+2)*L.length=r+(w+2)*(L.length+1:ℝ) by ring,pow_succ]
        ring

end YM.Integration.WilsonPositionProgramTrialTorusDifferences
