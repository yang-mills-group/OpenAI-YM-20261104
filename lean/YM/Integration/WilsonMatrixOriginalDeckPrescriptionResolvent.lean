import YM.Integration.WilsonMatrixOriginalDeckPrescriptionSeries
import YM.Integration.ActualOriginalFeeGrowth

/-! The real before-regulator polynomial bill for the full triangular correction at every finite horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckPrescriptionResolvent
open PhysicalNext.Repeat.Legato Finset MS MS.Land MS.Menus MS.Local.Physical
open WilsonMatrixOriginalDeckPrescription WilsonMatrixOriginalDeckRelative
open scoped Classical BigOperators Matrix
variable {G:Gauge} {B:Deck G} (Q:MS.Land.Prescription B) (h:ℕ)
local notation "I"=>Glyph B h

private theorem higher (μ:ℝ)(n:ℕ):∀ i j:I,j.grade < i.grade+n→ ((1-fees Q h μ 0)^n) i j=0:=by
  induction n with
  | zero =>
    intro i j lt
    have ne:i≠j:=by rintro rfl;omega
    simp [ne]
  | succ n ih =>
    intro i j lt;rw [pow_succ,Matrix.mul_apply];apply sum_eq_zero;intro l _
    by_cases low:l.grade < i.grade+n
    · rw [ih i l low,zero_mul]
    · have up:j.grade≤l.grade:=by omega
      simp [Matrix.one_apply,upper Q h μ l j up]

/-- A finite signed geometric polynomial computes the entire genuine zeroth inverse at any clock. -/
theorem geometric (μ:ℝ): (fees Q h μ 0)⁻¹=∑i∈Finset.range (h+1),(1-fees Q h μ 0)^i:=by
  let A:=1-fees Q h μ 0
  have vanish:A^(h+1)=0:=by ext i j;exact higher Q h μ (h+1) i j (by have:=j.memory;omega)
  have g:=geom_sum_mul_neg A (h+1)
  have back:1-A=fees Q h μ 0:=by dsimp [A];abel
  rw [back,vanish,sub_zero] at g
  calc (fees Q h μ 0)⁻¹ = 1*(fees Q h μ 0)⁻¹ := (one_mul _).symm
       _ = ((∑i∈Finset.range (h+1),A^i)*fees Q h μ 0)*(fees Q h μ 0)⁻¹ := by rw [g]
       _ = _ := by rw [Matrix.mul_assoc,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (WilsonMatrixOriginalDeckPrescription.original Q h μ)),mul_one]

/-- One clock polynomial covers all original fees through a declared physical order and all labelled rows. -/
theorem price (K:ℕ):∃ C:ℝ,0<C ∧ ∃d:ℕ,∀μ:ℝ,∀k≤K,
    WilsonMatrixOriginalDeckRelative.amount (fees Q h μ k)≤C*(1+‖μ‖)^d:=by
  obtain ⟨C,hC,d,paid⟩:=ActualOriginalFeeGrowth.bound B Q (fun i:I=>⟨i.size,i.2⟩) K
  let M:ℝ:=Fintype.card I
  refine ⟨(M^2+1)*C,by positivity,d,?_⟩;intro μ k hk
  have entry (i j:I): ‖fees Q h μ k i j‖≤C*(1+‖μ‖)^d:=by
    by_cases fits:i.size≤j.size
    · rw [fees,dif_pos fits];exact paid j k hk (resized i fits) μ
    · rw [fees,dif_neg fits,norm_zero];positivity
  calc _ ≤ ∑_i:I, ∑_j:I,C*(1+‖μ‖)^d :=sum_le_sum fun i _=>sum_le_sum fun j _=>entry i j
       _ = M^2*(C*(1+‖μ‖)^d) := by simp [M,pow_two];ring
       _ ≤ (M^2+1)*(C*(1+‖μ‖)^d) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
       _ = _ := by ring

end YM.Integration.WilsonMatrixOriginalDeckPrescriptionResolvent
