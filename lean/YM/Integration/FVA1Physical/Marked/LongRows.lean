import YM.Integration.FVA1Physical.Marked.StencilTests
import YM.Qlocal.Versal.Vienna

/-! Support-weighted accounting for the countable long rows of a physical
stencil. Every row keeps its own footprint, including paths that wind around
the lattice and paths joining different marked positions. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Marker Qlocal Qlocal.Quipu Quipu.Sonnet Push.AbsoluteSums
open scoped Classical BigOperators

variable {V I : Type} [DecidableEq V] {B : Census V} {G : Gauge}
variable {s : Senses B} {n : ℕ} {c : Side}

/-- The signed tests and the common root restriction may select different
rows. The same positive mass dominates every choice. -/
private theorem long_budget {fare cost : I → ℝ} {z v K C : ℝ} (h : SumBudget fare C)
    (keep : I → Prop) [DecidablePred keep] (test : I → Set.Icc (-1 : ℝ) 1) (hc : ∀ i, 0 ≤ cost i)
    (hK : 0 ≤ K) (hest : ∀ i, keep i → cost i * Real.exp (v*z) ≤ K * fare i) :
    SumBudget (fun i => if keep i then |(test i : ℝ)| * cost i else 0)
      ((K * Real.exp (-(v*z))) * C) := by
  refine budget_mono (budget_scale (mul_nonneg hK (Real.exp_nonneg _)) h) ?_ ?_
  · intro i
    split
    · exact mul_nonneg (abs_nonneg _) (hc i)
    · exact le_rfl
  · intro i
    by_cases hi : keep i
    · rw [if_pos hi]
      refine (mul_le_of_le_one_left (hc i) (abs_le.mpr (test i).property)).trans ?_
      calc
        cost i = (cost i * Real.exp (v*z)) * Real.exp (-(v*z)) := by
          rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        _ ≤ (K * fare i) * Real.exp (-(v*z)) := mul_le_mul_of_nonneg_right (hest i hi) (Real.exp_nonneg _)
        _ = _ := by ring
    · rw [if_neg hi]
      exact mul_nonneg (mul_nonneg hK (Real.exp_nonneg _)) (h.1 i)

/-- Simultaneous estimate for every regular derivative on the real support of
each long stencil. The sum includes the exponential price of each distinct
footprint. No cutoff is imposed on the length of a retained path. -/
theorem long_regular_rows (A : Album I s G n) (l : Lattice.Order) (x : Site c)
    (p : BudgetPoint) (r w : ℕ) (test : I → Set.Icc (-1 : ℝ) 1)
    (selected : I → Prop) {a d t v C : ℝ} (hA : A.Health (d+a+v) C)
    (ha : 0 < a) (ht : 0 ≤ t) (hv : 0 ≤ v) (hd : t/p.B ≤ d) :
    (∀ i, PayR p ((A i).cone l x) (|(test i : ℝ)| * (A i).Sus p r 0)
      ((test i : ℝ) • (A i).read x r)) ∧
    SumBudget (fun i => if selected i ∧ w < (A i).momentum then
      |(test i : ℝ)| * ((A i).Sus p r 0 * Real.exp (t * coverNumber p.B ((A i).cone l x))) else 0)
      ((p.threshold^n * Vase.humid G p.power p.order n r 0 (1+(essence s).card+n) t a *
        Real.exp (-(v * (w+1 : ℕ)))) * C) := by
  have hrow (i : I) := Vase.Suspend l (A i) x p ((A i).thin l x p.B_pos) r
  constructor
  · intro i
    exact (show PayR p ((A i).cone l x) ((A i).Sus p r 0) ((A i).read x r) from
      ⟨(hrow i).1, (hrow i).2.1, (hrow i).2.2⟩).z_m _
  · refine long_budget (v := v) (z := (w+1 : ℕ))
      (K := p.threshold^n * Vase.humid G p.power p.order n r 0 (1+(essence s).card+n) t a)
      (cost := fun i => (A i).Sus p r 0 * Real.exp (t * coverNumber p.B ((A i).cone l x)))
      hA (fun i => selected i ∧ w < (A i).momentum) test
      (fun i => mul_nonneg (hrow i).1 (Real.exp_nonneg _))
      (mul_nonneg (pow_nonneg p.threshold_pos.le _) (Vase.humid_nn _ _ _ _ _ _ _ _ ha)) ?_
    intro i hi
    rw [mul_assoc, ← Real.exp_add]
    apply le_trans ?_ (Vase.economical (u := v) l (A i) x p ((A i).thin l x p.B_pos) r ha ht hd)
    apply mul_le_mul_of_nonneg_left _ (hrow i).1
    exact Real.exp_le_exp.mpr (add_le_add_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hi.2) hv) _)

/-- Sharper support estimate for the values on the failed-mask sectors.
It uses the unmasked physical bound rather than an estimate restricted to
healthy fields. -/
theorem long_forced_rows (A : Album I s G n) (l : Lattice.Order) (x : Site c)
    (p : BudgetPoint) (r w : ℕ) (test : I → Set.Icc (-1 : ℝ) 1)
    (selected : I → Prop) {a d t v C : ℝ} (hA : A.Health (d+a+v) C)
    (ha : 0 < a) (ht : 0 ≤ t) (hv : 0 ≤ v) (hd : t/p.B ≤ d)
    (field : Config G c) :
    SumBudget (fun i => if selected i ∧ w < (A i).momentum ∧
      ¬Healthy p.threshold ((A i).cone l x) field then
      |(test i : ℝ)| * (|(A i).read x r field| * Real.exp (t * coverNumber p.B ((A i).cone l x)))
      else 0)
      ((Vase.ticketC G r n * Real.exp (t * (1+(essence s).card+n : ℕ)) *
        Real.exp (-(v * (w+1 : ℕ)))) * C) := by
  refine long_budget (v := v) (z := (w+1 : ℕ))
    (K := Vase.ticketC G r n * Real.exp (t * (1+(essence s).card+n : ℕ)))
    (cost := fun i => |(A i).read x r field| * Real.exp (t * coverNumber p.B ((A i).cone l x)))
    hA (fun i => selected i ∧ w < (A i).momentum ∧ ¬Healthy p.threshold ((A i).cone l x) field)
    test (fun _ => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))
    (mul_nonneg (Vase.ticketC_pos ..) (Real.exp_nonneg _)) ?_
  intro i hi
  let D := 1+(essence s).card+n
  let m := (A i).momentum
  let k := coverNumber p.B ((A i).cone l x)
  have hB : 0 < (p.B : ℝ) := Nat.cast_pos.mpr p.B_pos
  have hcov : (k : ℝ) ≤ D + (m : ℝ)/p.B := by
    have hc := (A i).paths_tube l x p.B_pos
    have hc' : (p.B : ℝ) * k ≤ (p.B : ℝ)*D+m := by exact_mod_cast hc
    calc
      (k : ℝ) ≤ ((p.B : ℝ)*D+m)/p.B := (le_div_iff₀ hB).mpr (by linarith only [hc'])
      _ = D + (m : ℝ)/p.B := by field_simp
  have hs : t * (k : ℝ) ≤ t * D + d*m := by
    refine (mul_le_mul_of_nonneg_left hcov ht).trans ?_
    rw [mul_add]
    apply add_le_add_right
    rw [show t * ((m : ℝ)/p.B) = (t/p.B)*m by ring]
    exact mul_le_mul_of_nonneg_right hd (by positivity)
  have hw : (w+1 : ℕ) ≤ m := hi.2.1
  have hread := (A i).paid x field ha r
  calc
    (|(A i).read x r field| * Real.exp (t*k)) * Real.exp (v*(w+1 : ℕ)) ≤
        (Vase.ticketC G r n * (A i).fare a) * Real.exp (t*k + v*(w+1 : ℕ)) := by
          rw [Real.exp_add, ← mul_assoc]
          gcongr
    _ ≤ (Vase.ticketC G r n * Real.exp (t*D)) * (A i).fare (d+a+v) := by
      unfold Vase.fare
      have hE : Real.exp (t*k+v*(w+1 : ℕ)) ≤ Real.exp (t*D)*Real.exp (d*m+v*m) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by
          have hvw : v*(w+1 : ℕ) ≤ v*m := mul_le_mul_of_nonneg_left (by exact_mod_cast hw) hv
          linarith)
      calc
        _ ≤ (Vase.ticketC G r n * ((A i).sizeC * Real.exp (a*m))) *
            (Real.exp (t*D)*Real.exp (d*m+v*m)) :=
          mul_le_mul_of_nonneg_left hE (mul_nonneg (Vase.ticketC_pos ..) (mul_nonneg (A i).nn_size (Real.exp_nonneg _)))
        _ = _ := by
          rw [show (d+a+v)*(A i).momentum = a*m + (d*m+v*m) by dsimp [m]; ring]
          simp only [Real.exp_add]
          ring

end YM.Integration.FVA1Physical.Marked
