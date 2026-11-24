import YM.Integration.FVA1Physical.Marked.ColorBudget
import YM.Integration.FVA1Physical.Sources.Round2.RentedCrossing

/-! A healthy collar of an individual source root suppresses every actual
surviving divided forced row carrying that root, even with flags elsewhere.
The remaining support exponent and the original divisor are explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Marker LocalComparison RG3.Script.Picnic Push.AbsoluteSums
open scoped Classical BigOperators
variable {I X : Type} [DecidableEq I] {B : Census I} {G : Gauge} {n : Side}
    {P : Rep G n} {o : I→Site n} {T : Taste X o P B} {w : I→ℝ} {κ a b : ℝ}

theorem actual_forced_collar (H : FullBudget P.p T w κ a b) (j : I) (r : ℕ) (reserve : ℝ)
    (hr : 0 ≤ reserve) (field : ℕ × ℕ → Config G n) (test : ℕ×ℕ→X)
    (S : Support n) (root : o j∈S)
    (healthy : ∀ i,Healthy P.p.threshold (halo (r*Push.GridApprox.Attach.leg P.p.B) S) (field i)) :
    SumBudget (fun i : ℕ×ℕ=>if j∈(T.menu.marks i.1 i.2).val then Poly.toll w (T.menu.marks i.1 i.2) *
      (Real.exp ((P.p.supportExponent-reserve)*coverNumber P.p.B (P.activities.forced i.1).support) *
        ‖T.menu.force (test i) i.1 i.2 (field i)‖) else 0)
      (Real.exp (-reserve*r)*(κ*b)) := by
  let f (i : ℕ×ℕ) := T.menu.force (test i) i.1 i.2 (field i)
  have paid := budget_scale (Real.exp_pos (-reserve*r)).le (H.forcedTotal j)
  apply budget_mono paid
  · intro i
    split <;> first | exact mul_nonneg (Poly.worth H.radii _).le (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) | exact le_rfl
  intro i
  by_cases mark : j∈(T.menu.marks i.1 i.2).val
  · simp only [if_pos mark,BudgetPoint.mass]
    let A := (P.activities.forced i.1).support
    let d := coverNumber P.p.B A
    let wt := Poly.toll w (T.menu.marks i.1 i.2)
    have pos : 0 ≤ wt := (Poly.worth H.radii _).le
    by_cases value : f i=0
    · change wt*(Real.exp ((P.p.supportExponent-reserve)*d)*‖f i‖) ≤
        Real.exp (-reserve*r)*(wt*(Real.exp (P.p.supportExponent*d)*H.black i))
      rw [value,norm_zero,mul_zero,mul_zero]
      exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg pos (mul_nonneg (Real.exp_nonneg _) (H.black_nonnegative i)))
    let active := (H.active (test i)).articles
    have supported : o j∈A := by
      rw [←T.root]
      exact active.retained i.1 i.2 (fun e=> value (congrFun e (field i))) j mark
    have eligible := active.keeps i.1 i.2 (field i) value
    obtain ⟨u,hu⟩ := (P.activities.forced i.1).inventory_ne
    have hsite : u∈A∩flags P.p.threshold (field i) := eligible.1 ▸ hu
    obtain ⟨inside,hit⟩ := Finset.mem_inter.mp hsite
    have outside : u∉halo (r*Push.GridApprox.Attach.leg P.p.B) S := fun h=>
      Finset.disjoint_left.mp (healthy i) h hit
    have far : r ≤ d := LocalLTE.Sail.Round2.cover_of_flag_outside supported root inside outside
    have ex : Real.exp ((P.p.supportExponent-reserve)*d) ≤
        Real.exp (-reserve*r)*Real.exp (P.p.supportExponent*d) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_left (Nat.cast_le.mpr far : (r:ℝ) ≤ (d:ℝ)) hr]
    change wt*(Real.exp ((P.p.supportExponent-reserve)*d)*‖f i‖) ≤
      Real.exp (-reserve*r)*(wt*(Real.exp (P.p.supportExponent*d)*H.black i))
    calc
      _ ≤ wt*((Real.exp (-reserve*r)*Real.exp (P.p.supportExponent*d))*H.black i) :=
        mul_le_mul_of_nonneg_left (mul_le_mul ex (H.forced (test i) i.1 i.2 (field i))
          (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)) pos
      _ = _ := by ring
  simp [mark]

end YM.Integration.FVA1Physical.Marked
