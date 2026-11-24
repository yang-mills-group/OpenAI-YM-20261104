import YM.Integration.WilsonCoherentFrozenStencil
import YM.Integration.WilsonCoherentFrozenTaylor

/-! The participating intrinsic links may vary in local Lie coordinates.
Every remaining link stays at its arbitrary original compact value. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentFrozenPrice
open Function Lattice Wilson RG Finset
open RGComparison.Core16 RGComparison.Core16.Spool
open WilsonCoherentFrozenStencil
open scoped Classical ContDiff Matrix.Norms.Frobenius NNReal

variable {G : Gauge} {I : Type} [Fintype I] (J : I → Lamp G)

def approximate (A : Finset (Slice J)) (b : Slice J → G.El) (z : Slice J → G.Color)
    (p : ℕ) (t : ℝ) :=
  ∑ j ∈ range (p+1), t^j • SignedChartTaylor.jet (mark J A b) z j

private theorem masked (A : Finset (Slice J)) (p : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (b : Slice J → G.El) (z : Slice J → G.Color) (t : ℝ), 0 < t → t*‖z‖<1 →
      ‖mark J A b (t•z)-approximate J A b z p t‖ ≤ C*(t*‖z‖)^(p+1) := by
  obtain ⟨F,hf,rep⟩ := WilsonCoherentFrozenStencil.original J A
  let base := fun b : Slice J → G.El => ((fun j => G.mat (b j)),(0 : Slice J → G.Color))
  have hb : Continuous base := by
    exact (continuous_pi fun j=> G.continuous_mat.comp (continuous_apply j)).prodMk continuous_const
  obtain ⟨C,hC,paid⟩ := WilsonCoherentFrozenTaylor.purchased F hf base hb p
  refine ⟨C,hC,?_⟩
  intro b z t ht rad
  let a := ((0 : Slice J → G.Mat),z)
  have size : ‖a‖=‖z‖ := by simp [a,Prod.norm_def]
  have eq (u : ℝ) : F (base b+u•a) = mark J A b (u•z) := by
    simpa [base,a] using rep b (u•z)
  have price := paid b a t ht (size ▸ rad)
  rw [size,eq] at price
  simpa only [SignedChartTaylor.jet,eq,approximate] using price

/-- One constant before every period, placement, active link set, original
compact exterior and angular direction. -/
theorem purchased (p : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : Side) (o : I → Site n)
    (A : Finset (Slice J)) (U : Config G n) (z : Slice J → G.Color)
    (t : ℝ), 0<t → t*‖z‖<1 →
    (∀ j ∈ A, U (legs J o j) = G.lieExp (t • z j)) →
    ‖tally J o U - approximate J A (U ∘ legs J o) z p t‖ ≤ C*(t*‖z‖)^(p+1) := by
  classical
  choose fee nonneg paid using fun A => masked J A p
  let f : Finset (Slice J) → ℝ≥0 := fun A => ⟨fee A,nonneg A⟩
  refine ⟨↑(univ.sup f),(univ.sup f).property,?_⟩
  intro n o A U z t ht rad changed
  have same : field J A (U ∘ legs J o) (t•z) = U ∘ legs J o := by
    funext j
    unfold field
    split
    · exact (changed _ ‹_›).symm
    · rfl
  have taken : mark J A (U ∘ legs J o) (t•z) = tally J o U := by
    rw [mark,same,exhibition]
  have bound : fee A ≤ (univ.sup f : ℝ≥0) := le_sup (f:=f) (mem_univ A)
  exact (taken ▸ paid A (U ∘ legs J o) z t ht rad).trans
    (mul_le_mul_of_nonneg_right bound (by positivity))

end YM.Integration.WilsonCoherentFrozenPrice
