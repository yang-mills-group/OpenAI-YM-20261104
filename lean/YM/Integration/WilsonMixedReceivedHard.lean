import YM.Integration.WilsonMixedTestTableau
import YM.QuadraticLocal.Tint.Patrol

/-! Insert the deposited forced array into the joint old and fresh test passport,
on the same configuration, amplitude, forced addresses and vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedReceivedHard
open Finset Function Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open Push Push.AbsoluteSums Next.Foundations
open WilsonMixedTestTableau WilsonMixedPassportRows
open private transport from YM.Integration.WilsonMixedTestTableau
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V] {J : Census V}
  {P Q : Passport n V} {point : BudgetPoint} {address : ℕ → ForcedAddress G n} {quiet : ℕ → Config G n → ℝ} {E F : V → Type}
  [∀ v, AddCommGroup (E v)] [∀ v, AddCommGroup (F v)] [∀ v, Module ℝ (E v)] [∀ v, Module ℝ (F v)]
  (A : ∀ v, Set (E v)) (B : ∀ v, Set (F v))
  (K : ∀ v, Submodule ℝ (E v)) (L : ∀ v, Submodule ℝ (F v))
  (old : Finset V) (zeroA : ∀ v, 0 ∈ A v)
  (H : Hard (Wallet A) point address quiet P.origin J)
  (file : Crown P.support A K H)

local notation "test" => left A B old zeroA
local notation "joined" => passport (owner P Q old)

include file
omit [Fintype V] [∀ v, AddCommGroup (F v)] [∀ v, Module ℝ (F v)] in
private theorem present (t : Wallet (actors A B)) (i : ℕ) (U : Config G n) (s : J.Mode)
    (live : (H.hard (test t) i U).part s ≠ 0) : s.val ⊆ old := by
  intro v hv
  by_contra absent
  apply live
  apply ((file.lesson i U).each s).advice.idle v hv (test t)
  simp only [left, leftAt, if_neg absent, Submodule.zero_mem]

/-- Each compulsory owner retains the full old polynomial evaluated on its actual projected test. -/
def posted : Hard (Wallet (actors A B)) point address quiet (joined).origin J where
  hard t := H.hard (test t)
  charged t := H.charged (test t)
  quiet t := H.quiet (test t)
  locality t i := { H.locality (test t) i with
    carry := by
      intro U s live v hv
      have belongs := present A B K old zeroA H file t i U s live hv
      change (owner P Q old v).origin v ∈ _
      rw [show owner P Q old v = P from if_pos belongs]
      exact (H.locality (test t) i).carry U s live v hv }

omit [Fintype V] in
theorem collared : Crown (joined).support (actors A B) (pieces K L) (posted (Q:=Q) A B K old zeroA H file) := by
  constructor
  intro i U
  constructor
  intro s
  refine ⟨?_, ?_⟩
  · apply transport ((file.lesson i U).each s).advice (leftAt A B old zeroA)
    · intro v _ x y z c d eq
      by_cases hv : v ∈ old
      · simp only [leftAt, if_pos hv]
        exact congrArg Prod.fst eq
      · simp [leftAt, hv]
    · intro v _ t ht
      by_cases hv : v ∈ old
      · simp only [leftAt, if_pos hv]
        exact ht.1
      · simp [leftAt, hv]
  · intro t active v hv
    have belongs := present A B K old zeroA H file t i U s active hv
    change (owner P Q old v).support v ⊆ _
    rw [show owner P Q old v = P from if_pos belongs]
    exact ((file.lesson i U).each s).announces (test t) active v hv

omit [Fintype V] [∀ v, AddCommGroup (F v)] [∀ v, Module ℝ (F v)] in
/-- Only true old modes contribute to the old forced salary, even with independent fresh radii. -/
theorem paid {w w' : V → ℝ} (positive : ∀ v, 0 < w v) (positive' : ∀ v, 0 < w' v)
    (fits : ∀ v ∈ old, w' v ≤ w v) {d : ℕ} {a k : ℝ} (h : H.Paid w d a k) :
    (posted (Q:=Q) A B K old zeroA H file).Paid w' d a k := by
  obtain ⟨f, covered, hit⟩ := h.wages
  let g (i : ℕ) : Poly J := fun s => if s.val ⊆ old then (f i).part s else 0
  have price (i : ℕ) : Poly.price w' (g i) ≤ Poly.price w (f i) := by
    apply Finset.sum_le_sum
    intro s _
    change Poly.toll w' s * ‖if s.val ⊆ old then (f i).part s else 0‖ ≤ _
    split
    next hs =>
      exact mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun v _ => (positive' v).le)
        (fun v hv => fits v (hs hv))) (norm_nonneg _)
    next =>
      rw [norm_zero, mul_zero]
      exact mul_nonneg (Poly.worth positive s).le (norm_nonneg _)
  refine ⟨g, ?_, ?_⟩
  · intro i t U s
    change ‖(H.hard (test t) i U).part s‖ ≤ _ ∧ _
    by_cases hs : s.val ⊆ old
    · simpa only [g, Poly.part, if_pos hs] using covered i (test t) U s
    · have vanished := not_ne_iff.mp (fun h => hs (present A B K old zeroA H file t i U s h))
      change H.hard (test t) i U s = 0 at vanished
      simp [g, Poly.part, hs, vanished]
  · intro x
    apply budget_mono (hit x)
    · intro i
      split
      · exact mul_nonneg (Poly.nonnegative positive' _) (Real.exp_pos _).le
      · exact le_rfl
    · intro i
      split
      · exact mul_le_mul_of_nonneg_right (price i) (Real.exp_pos _).le
      · exact le_rfl

end YM.Integration.WilsonMixedReceivedHard
