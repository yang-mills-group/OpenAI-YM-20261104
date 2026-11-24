import YM.Integration.WilsonOriginalDepositedRegularHearing
import YM.Integration.WilsonOriginalDepositedHardRate
import YM.QuadraticLocal.Tint.Patrol

/-! Enter the actual enrolled catalogue with its priced original regular and compulsory star entries. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalStarIncoming
open Function Finset Filter Lattice Wilson RG Source Marker Overlay QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Tint QuadraticLocal.Affinity
open WilsonOriginalDepositedHard WilsonOriginalDepositedRegular WilsonOriginalDepositedRegularWindow
open scoped Topology Classical BigOperators
variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d} {A : Hol G}
  {P : Rep G n} {V T I : Type} [DecidableEq V] {J : Census V} {o : V → Site n}
  (old : Incoming (Passport.point o) P T I J)
  (j : V) (q : Coefficient F n) (law : q.Format (o j) A P) (t : T → ℂ) (D : ℕ)

def enter : Incoming (Passport.point o) P T (I⊕ℕ) J where
  old := old.old.join (lamps j q law t (small P q D))
  hard := joined old.hard j q law t

theorem funded [Fintype V] (w : V → ℝ) (hw : ∀v, 0<w v) (ht : ∀x, ‖t x‖≤1) {κ B k h : ℝ}
    (original : q.remBound (o j) P κ B)
    (regular : old.old.Paid w P.p.B (P.p.supportExponent+1+1) k)
    (forced : old.hard.Paid w P.p.B P.p.supportExponent h) :
    (enter old j q law t D).old.Paid w P.p.B (P.p.supportExponent+1+1)
      (k+ Real.exp (3*D)*WilsonRetainedMarkedInletRegular.cost P.p*(w j*B)) ∧
    (enter old j q law t D).hard.Paid w P.p.B P.p.supportExponent (h+w j*(κ*B)) := by
  constructor
  · apply Lamps.joinPaid regular
    rw [show P.p.supportExponent+1+1=P.p.supportExponent+2 by ring]
    exact short j q law t D w hw ht original
  exact WilsonOriginalDepositedHard.paid old.hard j q law t w hw forced ht original

section
variable {Y : V → Type} [∀ i, AddCommGroup (Y i)] {𝕜 : Type} [RCLike 𝕜]
  [NormedAlgebra 𝕜 ℂ] [∀ i, Module 𝕜 (Y i)] (C : ∀ i, Set (Y i))
  (K : ∀ i, Submodule 𝕜 (Y i)) (old₀ : Incoming (Passport.point o) P (Wallet C) I J)
  (a : Wallet C → ℂ)

theorem compatible (t₀ : Taut (Passport.point o).support C K old₀.old)
    (h₀ : Crown (Passport.point o).support C K old₀.hard) (affine : Attn K C {j} a) :
    Taut (Passport.point o).support C K (enter old₀ j q law a D).old ∧
    Crown (Passport.point o).support C K (enter old₀ j q law a D).hard := by
  have smooth := taut (J:=J) j q law C K a (small P q D) affine
  refine ⟨⟨?_,?_⟩,WilsonOriginalDepositedHardTable.crown j q law C K old₀.hard a h₀ affine⟩
  · intro i
    cases i with
    | inl i => exact t₀.house i
    | inr i => exact smooth.house i
  · intro i U
    cases i with
    | inl i => exact t₀.adv i U
    | inr i => exact smooth.adv i U
end

end YM.Integration.WilsonOriginalStarIncoming
