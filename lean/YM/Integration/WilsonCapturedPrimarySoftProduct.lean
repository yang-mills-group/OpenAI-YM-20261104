import YM.Integration.WilsonCenteredCaptureLampRoster
import YM.RG08.Ballast.Ribbons

/-! Absolute and signed finite products of the countable row rosters. Each
connected block may use a different addressed subtype of the original lamps. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimarySoftProduct
open Function Finset RG Lattice Wilson Marker QuadraticLocal Ac Push.Local Corona Push.AbsoluteSums
open scoped Classical BigOperators
variable {k : ℕ}

theorem budget (A : Fin k → Type) (price : Fin k → ℝ) {e : (j : Fin k) → A j → ℝ}
    (paid : ∀ j, SumBudget (e j) (price j)) :
    SumBudget (fun v : (j : Fin k) → A j => ∏ j,e j (v j)) (∏ j,price j) := by
  induction k with
  | zero => exact budget_finite (fun _=>by simp) (by simp)
  | succ k ih =>
    let Z := Fin.consEquiv A
    have whereat (v : (j : Fin (k+1)) → A j) : Z.symm v=(v 0,fun (j : Fin k)=>v j.succ) := by
      apply Z.injective
      rw [Z.apply_symm_apply]
      funext j
      refine Fin.cases ?_ (fun _=>?_) j <;> rfl
    have h := budget_pull Z.symm Z.symm.injective (budget_prod (paid 0)
      (ih (fun j=>A j.succ) _ (fun j=>paid j.succ)))
    simp only [whereat] at h
    simp_rw [Fin.prod_univ_succ (n:=k)]
    exact h

theorem product (A : Fin k → Type) (f : (j : Fin k) → A j → ℂ)
    (paid : ∀ j,Summable (f j)) :
    ∑' v : (j : Fin k)→A j, ∏ j,f j (v j) = ∏ j,∑' i,f j i := by
  induction k with
  | zero => simp [tsum_fintype]
  | succ k ih =>
    let Z := Fin.consEquiv A
    have fees (j : Fin k) : SumBudget (fun i => ‖f j.succ i‖) (∑' i,‖f j.succ i‖) :=
      ⟨fun _=>norm_nonneg _, (paid _).norm, le_rfl⟩
    have h := (budget _ _ fees).2.1
    have norms : Summable (fun v : (j : Fin k)→A j.succ => ‖∏ j,f j.succ (v j)‖) := by
      simpa only [norm_prod] using h
    rw [←Z.tsum_eq]
    simp_rw [Fin.prod_univ_succ (n:=k)]
    rw [←ih (fun j=>A j.succ) (fun j=>f j.succ) (fun j=>paid j.succ)]
    exact (tsum_mul_tsum_of_summable_norm (paid 0).norm norms).symm

theorem signed (A : Fin k → Type) (f : (j : Fin k)→A j→ℂ) (z : Fin k→ℂ)
    (paid : ∀ j,HasSum (f j) (z j)) :
    HasSum (fun v : (j : Fin k) → A j=>∏ j,f j (v j)) (∏ j,z j) := by
  have fees j : SumBudget (fun v=>‖f j v‖) (∑' v,‖f j v‖) :=
    ⟨fun _=>norm_nonneg _, (paid j).summable.norm, le_rfl⟩
  have h : Summable (fun v : (j : Fin k) → A j=>‖∏ j,f j (v j)‖) := by
    simpa only [norm_prod] using (budget A _ fees).2.1
  have value := product A f (fun j=>(paid j).summable)
  simp_rw [fun j=>(paid j).tsum_eq] at value
  rw [←value]
  exact h.of_norm.hasSum

end YM.Integration.WilsonCapturedPrimarySoftProduct
