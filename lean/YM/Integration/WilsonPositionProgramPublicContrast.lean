import YM.Integration.WilsonPositionProgramPublicOriented
import YM.Integration.WilsonThermometerUnitFilingFourSquareGram

/-! Four signed, physically reflected Wilson pairings with independent
finite rosters and regulator-dependent numerical weights on the two arms. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicContrast
open Filter Extraction Spec Table WilsonThermometerUnitFilingFourSquare
open WilsonThermometerUnitFilingFourSquareGram
open scoped Topology Classical BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]
def charge (a : I → ℂ) := ∑ i, ‖a i‖
def assay (a : I → ℂ) (b : J → ℂ) (q : I → J → ℂ) :=
  ∑ i, ∑ j, (star (a i)*b j)*q i j

theorem price (a : I → ℂ) (b : J → ℂ) (q : I → J → ℂ) :
    ‖assay a b q‖ ≤ charge a*charge b*‖q‖ := by
  calc
    _ ≤ ∑ i, ‖∑ j, (star (a i)*b j)*q i j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖a i‖*‖b j‖*‖q‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul,norm_star]
      exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm (q i) j).trans (norm_le_pi_norm q i)) (by positivity)
    _ = _ := by simp [charge,Finset.sum_mul,Finset.mul_sum]; exact Finset.sum_comm

variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
    {l : Filter (ℕ×ℕ)} [l.NeBot] {d : ℕ} (F : Final C f S) (s : Signed)
    {x : I → S.Field d} {y : J → S.Field d}
    (X : (i : I) → Bool → Arm C S l d (x i)) (Y : (j : J) → Bool → Arm C S l d (y j))
    (test : I → J → Test 2)

def corner (u : ℕ×ℕ) (i : I) (j : J) (a b : Bool) :=
  marked (pair F s (X i) (Y j)) ![a,b] (test i j) u

def table (u : ℕ×ℕ) (i : I) (j : J) : ℂ :=
  (corner F s X Y test u i j false false - corner F s X Y test u i j false true) -
    (corner F s X Y test u i j true false - corner F s X Y test u i j true true)

theorem original (order : l ≤ f.fuse)
    (a : ℕ×ℕ → I → ℂ) (b : ℕ×ℕ → J → ℂ) {K T : ℝ}
    (ha : ∀ᶠ z in l, charge (a z) ≤ K) (hb : ∀ᶠ z in l, charge (b z) ≤ T) :
    Tendsto (fun z => assay (a z) (b z) (table F s X Y test z)) l (𝓝 0) := by
  have cells : Tendsto (table F s X Y test) l (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact WilsonThermometerUnitFilingFourSquare.original F order (pair F s (X i) (Y j)) (test i j)
  have tends : Tendsto (fun z => K*T*‖table F s X Y test z‖) l (𝓝 0) := by
    simpa only [norm_zero,mul_zero] using cells.norm.const_mul (K*T)
  apply squeeze_zero_norm' _ tends
  filter_upwards [ha,hb] with z az bz
  apply (price _ _ _).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul az bz
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) ((Finset.sum_nonneg fun _ _ => norm_nonneg _).trans az)) (norm_nonneg _)

end YM.Integration.WilsonPositionProgramPublicContrast
