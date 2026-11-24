import YM.Integration.WilsonMatrixOriginalDeckRelative

/-! A signed telescoping formula and entrywise costs for an arbitrary full trial transport. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckError
open Filter Set Finset Extraction Extraction.Order Spec Climb MS MS.Local.Physical MS.Menus MS.Land MS.Theater FVA2
open RG17 PhysicalNext.Repeat.Legato WilsonMatrixOriginalDeckPath WilsonMatrixOriginalDeckRelative
open private identity from YM.Integration.WilsonMatrixOriginalDeckCutoff
open private matrixSize vectorSize image_size from YM.Integration.WilsonMatrixOriginalDeckInverse
open scoped Classical BigOperators Matrix

/-- Later targets appear on the left, with the full trial prefix retained on the right of its error. -/
theorem telescope {X:Type*} [Ring X] (U:ℕ→ℕ→X) (V:ℕ→X)
    (same:∀i,U i i=1) (link:∀i j k,U i j*U j k=U i k) (n:ℕ) :
    steps V n-U n 0=∑i∈range n,U n (i+1)*(V i-U (i+1) i)*steps V i := by
  induction n with
  | zero => simp [steps,same]
  | succ n ih =>
    have rest : U (n+1) n*(∑i∈range n,U n (i+1)*(V i-U (i+1) i)*steps V i) =
        ∑i∈range n,U (n+1) (i+1)*(V i-U (i+1) i)*steps V i := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      rw [←link (n+1) n (i+1)]
      simp only [mul_assoc]
    rw [sum_range_succ,same,one_mul,←rest,←ih,←link (n+1) n 0]
    simp only [steps,mul_sub,sub_mul]
    abel

variable {I:Type*} [Fintype I]

theorem add_cost (A B:Matrix I I ℂ) : amount (A+B)≤amount A+amount B := by
  unfold WilsonMatrixOriginalDeckRelative.amount
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro i _
  rw [←sum_add_distrib]
  exact sum_le_sum fun j _=>norm_add_le (A i j) (B i j)

theorem product_cost (A B:Matrix I I ℂ) : amount (A*B)≤amount A*amount B := by
  classical
  unfold WilsonMatrixOriginalDeckRelative.amount
  calc (∑i,∑j,‖(A*B) i j‖) = ∑j,vectorSize (A *ᵥ fun k=>B k j) := sum_comm
       _ ≤ ∑j,matrixSize A*vectorSize (fun k=>B k j) := sum_le_sum fun j _=>image_size A (fun k=>B k j)
       _ = _ := by rw [←mul_sum];congr 1;exact sum_comm

theorem sum_cost {T:Type*} (s:Finset T) (Z:T→Matrix I I ℂ) : amount (∑i∈s,Z i) ≤ ∑i∈s,amount (Z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [WilsonMatrixOriginalDeckRelative.amount]
  | @insert i s hi ih =>
    rw [sum_insert hi,sum_insert hi]
    exact (add_cost _ _).trans (add_le_add le_rfl ih)

theorem nonneg (Z:Matrix I I ℂ) : 0≤amount Z := sum_nonneg fun i _=>sum_nonneg fun j _=>norm_nonneg (Z i j)

variable {G:Gauge} (R:Run G) (B:Deck G) {S:Table R.family.book} (J:ℝ→PhysMS.tower S) (h:ℕ)

/-- Exact signed error of a proposed high-to-low field coefficient after the full height is transported. -/
theorem original (r:ℕ→ℝ) (V:ℕ→Matrix (Glyph B h) (Glyph B h) ℂ) (n:ℕ) :
    let U := fun i j=>WilsonMatrixOriginalDeckMixed.change B J h (r i) (r j)
    steps V n-U n 0=∑i∈range n,U n (i+1)*(V i-U (i+1) i)*steps V i :=
  telescope _ V (fun i=>identity R B J h (r i))
    (fun i j k=>WilsonMatrixOriginalDeckReturn.compose R B J h (r i) (r j) (r k)) n

end YM.Integration.WilsonMatrixOriginalDeckError
