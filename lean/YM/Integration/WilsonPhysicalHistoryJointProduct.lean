import YM.Integration.WilsonPhysicalHistoryFieldAnchors

/-! Apply the original finite angular Cauchy-product estimate to all marked
incoming factors before the joint normalized vacuum expectation. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryJointProduct
open Function Finset Lattice RG Precision Wilson MSbar MSbar.Whisk MSbar.Cacao
open scoped Classical BigOperators
variable {I σ : Type} [Fintype σ] {n : Side}

def factor (p m : ℕ) (t : ℝ) : ℝ := ((p+1:ℕ):ℝ)*(2:ℝ)^m*t

/-- All couplings of an arbitrary finite product of *incoming* fields. -/
theorem finite (U : σ→Site n) (z : Site n) {a t : ℝ} (a0 : 0≤a)
    (s m p d : ℕ) (T : I→PowerSeries (Pot σ)) (S : Finset I)
    (leaf : ∀ j ∈ S, ∀ e ≤ p, Whisk.Vault U {z} a s m 0 (PowerSeries.coeff e (T j)) t ∧
      (PowerSeries.coeff e (T j)).totalDegree≤d) :
    ∀ e ≤ p, Whisk.Vault U {z} a s m 0 (PowerSeries.coeff e (∏ j∈S,T j))
      ((factor p m t)^S.card) ∧ (PowerSeries.coeff e (∏ j∈S,T j)).totalDegree≤S.card*d := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro e _
    simp only [Finset.prod_empty,Finset.card_empty,pow_zero,Nat.zero_mul]
    by_cases he : e=0
    · subst e
      have base : Whisk.Vault U {z} a s m 0 (MvPolynomial.C (1:ℝ)) |(1:ℝ)| := Bout.VaultC _
      simpa using And.intro base (le_refl (0:ℕ))
    · have zc : PowerSeries.coeff e (1 : PowerSeries (Pot σ)) = 0 := by
        simp [PowerSeries.coeff_one,he]
      rw [zc]
      have zero : Whisk.Vault U {z} a s m 0 (MvPolynomial.C (0:ℝ)) |(0:ℝ)| := Bout.VaultC _
      have zero' : Whisk.Vault U {z} a s m 0 0 0 := by simpa using zero
      exact ⟨⟨zero_le_one,fun k hk=>(zero'.2 k hk).trans zero_le_one⟩,by simp⟩
  | @insert j S fresh ih =>
    intro e he
    have old := ih (fun k hk=>leaf k (Finset.mem_insert_of_mem hk))
    have added := Bout.entire (T j) (∏ k∈S,T k) a0 (leaf j (Finset.mem_insert_self ..)) old e he
    rw [Finset.prod_insert fresh,Finset.card_insert_of_notMem fresh]
    constructor
    · have paid : ((p+1:ℕ):ℝ)*(2^m*(t*(factor p m t)^S.card)) =
          (factor p m t)^(S.card+1) := by rw [pow_succ];unfold factor;ring
      rw [←paid]
      exact added.1
    · exact added.2.trans_eq (by rw [Nat.succ_mul]; omega)
end YM.Integration.WilsonPhysicalHistoryJointProduct

