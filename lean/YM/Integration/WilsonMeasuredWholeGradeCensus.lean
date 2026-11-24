import YM.Integration.WilsonMeasuredOriginalCatalogueUnion

/-! Attach the actual incoming coupling grade to both sides of the finite
signed group catalogue before the short calculation.  All old addresses and
the deposited pupil are the same at every grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredWholeGradeCensus
open Finset Lattice Wilson RG Marker Multi QuadraticLocal QuadraticLocal.Earn AllOrder AllOrder.Floe
open Comparison.RG02 WilsonEmittedFiledGerm
open QuadraticLocal.Sunrise Laurent FVA1Physical.TwoReset
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{A V:Type}[Fintype A][DecidableEq V]
  {P:A→Passport n V}{J:Census V}{I X:A→Type}
  (M:(a:A)→I a→Row (P a) J G (X a))(grades:A→V→ℕ)(x:(a:A)→X a)
  (ν:A→ℕ)(s:Hot J)(L:A→Layout G)(tape:A→Finset Age)(k:ℕ)

omit [Fintype A] in
theorem shifted (i:ℕ)(v:Directions G n)(a:A):
    price M grades x (fun a=>k+ν a) s L tape i v a =
      if k ≤ i then price M grades x ν s L tape (i-k) v a else 0 :=by
  by_cases live:k ≤ i
  · rw [if_pos live]
    unfold price
    have flag:k+ν a+(Launch.index J (grades a) s.val+1) ≤ i ↔
        ν a+(Launch.index J (grades a) s.val+1) ≤ i-k:=by omega
    have rank:i-(k+ν a)-(Launch.index J (grades a) s.val+1)=
        (i-k)-ν a-(Launch.index J (grades a) s.val+1):=by omega
    simp only [flag,rank]
  · rw [if_neg live]
    unfold price
    dsimp only
    rw [if_neg (by omega)]

theorem funded (c:A→ℝ)(pole order:ℕ)(live:k ≤ order)
    (old:∀i<pole+(order-k)+1,∀v:Directions G n, (∑a,c a • price M grades x ν s L tape i v a)=0)
    (i:ℕ)(within:i<pole+order+1)(v:Directions G n):
    (∑a,c a • price M grades x (fun a=>k+ν a) s L tape i v a)=0 :=by
  simp_rw [shifted]
  by_cases h:k ≤ i
  · simp only [if_pos h]
    exact old _ (by omega) v
  · simp [h]

theorem field (c:A→ℝ)(g:ℝ)(S:J.Mode)(U:Config G n):
    (∑a,c a • (g^(k+ν a) • (Spill.Foundry.uncut (M a) g (x a) U).part S))=
      (g:ℂ)^k*(∑a,c a • (g^(ν a) • (Spill.Foundry.uncut (M a) g (x a) U).part S)):=by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [pow_add,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_pow]
  ring

end YM.Integration.WilsonMeasuredWholeGradeCensus
end
