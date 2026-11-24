import YM.Integration.WilsonThermometerCenteredAlgebra
import YM.Integration.WilsonThermometerCenteredScalar

/-! A local inverse may depend on the cutoff and on all three genuine fine
sites. Take the connected coefficient before summing the tested cells.
Only the proper quotient faces contribute products of errors. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerFiniteConnectedRemainder
open Finset Marker Extra.Trajectories Comparison.RG02
open WilsonThermometerCenteredScalar WilsonThermometerCenteredAlgebra
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)

/-- All three indices refer to the same cell and to its same finite inverse. -/
theorem cell (F Q : Poly J) (fu : F.part (J).quiet = 1) (qu : Q.part (J).quiet = 1) :
    let E := read (total F Q)
    read (Extra.Trajectories.connected F) univ - read (Extra.Trajectories.connected Q) univ =
      E univ - (E {0,1}*E {2} + E {0,2}*E {1} + E {1,2}*E {0}) +
        2*(E {0}*E {1}*E {2}) := by
  have normalized := normed F Q fu qu
  have glued := congrArg (fun A : Poly J => read A univ)
    (Comparison.RG02.connected_product normalized qu)
  rw [restore F Q qu] at glued
  change read (Extra.Trajectories.connected F) univ =
    read (Extra.Trajectories.connected (total F Q)) univ +
      read (Extra.Trajectories.connected Q) univ at glued
  rw [glued,add_sub_cancel_right,WilsonThermometerCenteredScalar.three _ normalized]

variable {ι : Type*} [Fintype ι]

private theorem pair (w f g : ι → ℂ) {A B : ℝ} (ha : 0 ≤ A) (hb : 0 ≤ B)
    (p : ∑ i, ‖w i‖*‖f i‖^2 ≤ A^2) (q : ∑ i, ‖w i‖*‖g i‖^2 ≤ B^2) :
    ‖∑ i, w i*(f i*g i)‖ ≤ A*B := by
  let x (i : ι) := Real.sqrt ‖w i‖ * ‖f i‖
  let y (i : ι) := Real.sqrt ‖w i‖ * ‖g i‖
  have xy (i : ι) : x i*y i = ‖w i‖*(‖f i‖*‖g i‖) := by
    dsimp [x,y]
    rw [show Real.sqrt ‖w i‖*‖f i‖*(Real.sqrt ‖w i‖*‖g i‖) =
      (Real.sqrt ‖w i‖)^2*(‖f i‖*‖g i‖) by ring,Real.sq_sqrt (norm_nonneg _)]
  have px : (∑ i, (x i)^2) ≤ A^2 := by simpa [x,mul_pow,Real.sq_sqrt] using p
  have py : (∑ i, (y i)^2) ≤ B^2 := by simpa [y,mul_pow,Real.sq_sqrt] using q
  calc
    ‖∑ i, w i*(f i*g i)‖ ≤ ∑ i, x i*y i := by
      simpa only [xy,norm_mul] using norm_sum_le univ (fun i => w i*(f i*g i))
    _ ≤ A*B := by
      apply le_of_sq_le_sq _ (mul_nonneg ha hb)
      rw [mul_pow]
      exact (Finset.sum_mul_sq_le_sq_mul_sq univ x y).trans
        (mul_le_mul px py (sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _))

private theorem cubic (w x y z : ι → ℂ) {A : ℝ}
    (px : ∑ i, ‖w i‖*‖x i‖^3 ≤ A^3) (py : ∑ i, ‖w i‖*‖y i‖^3 ≤ A^3)
    (pz : ∑ i, ‖w i‖*‖z i‖^3 ≤ A^3) : ‖∑ i, w i*(x i*y i*z i)‖ ≤ A^3 := by
  have amgm (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
      a*b*c ≤ (a^3+b^3+c^3)/3 := by
    nlinarith [mul_nonneg (add_nonneg (add_nonneg ha hb) hc)
      (add_nonneg (add_nonneg (sq_nonneg (a-b)) (sq_nonneg (b-c))) (sq_nonneg (c-a)))]
  calc
    _ ≤ ∑ i, ‖w i‖*(‖x i‖*‖y i‖*‖z i‖) := by
      simpa only [norm_mul] using norm_sum_le univ (fun i => w i*(x i*y i*z i))
    _ ≤ (∑ i, ‖w i‖*(‖x i‖^3+‖y i‖^3+‖z i‖^3)/3) := by
      apply sum_le_sum
      intro i _
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (amgm _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    _ ≤ A^3 := by
      simp only [mul_add,← Finset.sum_div,Finset.sum_add_distrib]
      linarith

/-- The complete signed linear hearing gives the first term. The two and
three factor expenses are with respect to the absolute mass of the
actual cell test, with no cell-count multiplier. -/
theorem tested (w : ι → ℂ) (F Q : ι → Poly J)
    (fu : ∀ i, (F i).part (J).quiet = 1) (qu : ∀ i, (Q i).part (J).quiet = 1)
    (E A B C : ℝ) (ha : 0 ≤ A) (hb : 0 ≤ B)
    (head : ‖∑ i, w i*(total (F i) (Q i)).part full‖ ≤ E)
    (two : ∀ s : Finset (Fin 3), s.card = 2 →
      ∑ i, ‖w i‖*‖read (total (F i) (Q i)) s‖^2 ≤ A^2)
    (one : ∀ v : Fin 3, ∑ i, ‖w i‖*‖read (total (F i) (Q i)) {v}‖^2 ≤ B^2)
    (three : ∀ v : Fin 3, ∑ i, ‖w i‖*‖read (total (F i) (Q i)) {v}‖^3 ≤ C^3) :
    ‖∑ i, w i*(read (Extra.Trajectories.connected (F i)) univ -
      read (Extra.Trajectories.connected (Q i)) univ)‖ ≤ E + 3*(A*B) + 2*C^3 := by
  let s (v : Finset (Fin 3)) (i : ι) := read (total (F i) (Q i)) v
  have pairs (v : Finset (Fin 3)) (i : Fin 3) (hv : v.card = 2) :
      ‖∑ j, w j*(s v j*s {i} j)‖ ≤ A*B := pair w _ _ ha hb (two v hv) (one i)
  have trip : ‖∑ j, w j*(s {0} j*s {1} j*s {2} j)‖ ≤ C^3 :=
    cubic w _ _ _ (three 0) (three 1) (three 2)
  have form : (∑ i, w i*(read (Extra.Trajectories.connected (F i)) univ -
      read (Extra.Trajectories.connected (Q i)) univ)) =
      (∑ i, w i*s univ i) - ((∑ i, w i*(s {0,1} i*s {2} i)) +
        (∑ i, w i*(s {0,2} i*s {1} i)) + (∑ i, w i*(s {1,2} i*s {0} i))) +
        (2 : ℂ)*(∑ i, w i*(s {0} i*s {1} i*s {2} i)) := by
    rw [Finset.mul_sum]
    simp only [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rw [cell (F i) (Q i) (fu i) (qu i)]
    dsimp [s]
    ring
  have H : ‖∑ i, w i*s univ i‖ ≤ E := head
  rw [form]
  calc
    _ ≤ (‖∑ i, w i*s univ i‖ +
        ((‖∑ i, w i*(s {0,1} i*s {2} i)‖ + ‖∑ i, w i*(s {0,2} i*s {1} i)‖) +
          ‖∑ i, w i*(s {1,2} i*s {0} i)‖)) + 2*‖∑ i, w i*(s {0} i*s {1} i*s {2} i)‖ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · apply (norm_sub_le ..).trans
        apply add_le_add le_rfl
        exact (norm_add_le ..).trans (add_le_add (norm_add_le ..) le_rfl)
      · rw [norm_mul]
        norm_num
    _ ≤ _ := by
      linarith [pairs {0,1} 2 (by decide),pairs {0,2} 1 (by decide),pairs {1,2} 0 (by decide)]

end YM.Integration.WilsonThermometerFiniteConnectedRemainder
