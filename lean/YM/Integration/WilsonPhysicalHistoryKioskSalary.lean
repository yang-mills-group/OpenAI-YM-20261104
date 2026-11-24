import YM.Integration.WilsonPhysicalHistoryKioskCollar

/-! Bound the full rough change using the three already registered regular
salaries at their own support exponent. This avoids charging the whole
re-expression ball to its value. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryKioskSalary
open Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums QuadraticLocal
open scoped Classical BigOperators

variable {V I T : Type*} [DecidableEq V] {G : Gauge} {n : Side} {p : BudgetPoint}
  {Z : Census V} {o : V → Site n} {w : V → ℝ} {B : ℕ} {A b : ℝ}

theorem occupied (L : Lamps T I G p o Z) (pos : ∀ v, 0<w v) (expo : 0≤A)
    (budget : L.Paid w B A b) (s : Z.Mode) (v : V) (root : v∈s.val) (t : T) (U : Config G n) :
    Poly.toll w s * ‖(L.log t U).part s‖ ≤ Real.exp (-A*(coverNumber B (s.val.image o) : ℝ))*b := by
  obtain ⟨cap,nonnegative,charge,paid⟩ := budget.budget
  let D := coverNumber B (s.val.image o)
  let f := Real.exp (-A*(D:ℝ))
  have major := budget_scale (Real.exp_pos (-A*(D:ℝ))).le (paid (o v))
  have rows : SumBudget (fun i => Poly.toll w s*‖(L.frame i t U).part s‖) (f*b) := by
    apply budget_mono major (fun _ => mul_nonneg (Poly.worth pos s).le (norm_nonneg _))
    intro i
    by_cases h : s=L.mode i
    · subst s
      have ground : (L.mode i).val.image o ⊆ L.ground i := image_subset_iff.mpr (L.roots i)
      have extent : D≤coverNumber B (L.ground i) := Corona.cover_mono ground B
      have exponent : 1≤f*Real.exp (A*coverNumber B (L.ground i)) := by
        rw [show f=Real.exp (-A*(D:ℝ)) from rfl,←Real.exp_add,Real.one_le_exp_iff]
        have order := mul_le_mul_of_nonneg_left
          (show (D:ℝ)≤coverNumber B (L.ground i) by exact_mod_cast extent) expo
        linarith
      have bounded := L.light_size i t U (charge i t (L.address i).site (L.address i).anchor)
      change _ ≤ f*(if o v∈L.ground i then _ else 0)
      rw [if_pos (show o v∈L.ground i from L.roots i v root)]
      simp only [Lamps.frame,Poly.part_send]
      exact (mul_le_mul_of_nonneg_left bounded (Poly.worth pos _).le).trans
        ((le_mul_of_one_le_right (mul_nonneg (Poly.worth pos _).le (nonnegative i)) exponent).trans_eq (by ring))
    · simpa [Lamps.frame,Poly.part_send,h] using (major.1 i)
  have ht := Poly.worth pos s
  have integrable : Summable (fun i => ‖(L.frame i t U).part s‖) :=
    (summable_mul_left_iff ht.ne').mp rows.2.1
  rw [Lamps.log,Poly.share (budget.sums expo pos t U) s]
  apply (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm integrable) ht.le).trans
  rw [←tsum_mul_left]
  exact rows.2.2

theorem signed {I₁ I₀ : Type*} (raw : Lamps T I G p o Z)
    (filed : Lamps T I₁ G p o Z) (residual : Lamps T I₀ G p o Z)
    (pos : ∀ v, 0<w v) (expo : 0≤A) {b₁ b₀ : ℝ}
    (rawPaid : raw.Paid w B A b) (filedPaid : filed.Paid w B A b₁)
    (residualPaid : residual.Paid w B A b₀)
    (s : Z.Mode) (v : V) (root : v∈s.val) (t : T) (U : Config G n) :
    Poly.toll w s * ‖(raw.log t U-filed.log t U-residual.log t U).part s‖ ≤
      Real.exp (-A*(coverNumber B (s.val.image o) : ℝ))*(b+b₁+b₀) := by
  have r := occupied raw pos expo rawPaid s v root t U
  have y := occupied filed pos expo filedPaid s v root t U
  have z := occupied residual pos expo residualPaid s v root t U
  change _ * ‖((raw.log t U).part s-(filed.log t U).part s)-(residual.log t U).part s‖ ≤ _
  have triangle := (norm_sub_le ((raw.log t U).part s-(filed.log t U).part s) ((residual.log t U).part s)).trans
    (add_le_add (norm_sub_le ((raw.log t U).part s) ((filed.log t U).part s)) le_rfl)
  calc
    _ ≤ Poly.toll w s * ((‖(raw.log t U).part s‖+‖(filed.log t U).part s‖)+‖(residual.log t U).part s‖) :=
      mul_le_mul_of_nonneg_left triangle (Poly.worth pos s).le
    _ ≤ _ := by rw [mul_add,mul_add,mul_add,mul_add]; exact add_le_add (add_le_add r y) z

end YM.Integration.WilsonPhysicalHistoryKioskSalary
end
