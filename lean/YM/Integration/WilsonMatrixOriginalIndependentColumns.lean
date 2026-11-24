import YM.Integration.WilsonMatrixTicketLanesRetainedFare
import YangMills.WilsonProof.NativeSupport.YM.MS.Theater.Horizon
import YM.TraceExtension.Terrace.Insert

/-! Exact independent MS coordinates for every bare finite Wilson label at the first positive grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalIndependentColumns
open Lattice Wilson RG Precision Maxwell Labels FVA2 FVA2.Warehouse
open Function Finset MS.Local.Physical MS.Theater MS.Menus
open WilsonMatrixTicketLanesNativePrices
open scoped Classical BigOperators

variable {G:Gauge} (V:Warehouse G) (B:Deck G) (d:ℕ)

/-- The label of the independent source in the full engineering horizon. -/
def field (i:Glyph B d):Label G d:=
  raiseLabel G (Nat.le_of_lt_succ i.1.isLt) (Warehouse.label B i.1.val i.2.1.val i.2.2)

/-- Undo the finite Wilson Wick matrix before evaluating on genuine Maxwell jets. -/
def raw : (V.scene d).Coeff ≃ₗ[ℂ] Label G d :=
  ((V.scopeW d).conversion (inftyQ G)).trans (V.scene d).coords.symm

def shell:(V.scene d).Coeff→ₗ[ℂ]shellSector G d:=
  (Maxwell.snap V.F d).comp ((V.scopeW d).conversion (inftyQ G)).toLinearMap

def column (i:Glyph B d):(V.scene d).Coeff:=
  (V.scopeW d).inverse (inftyQ G) ((V.scene d).coords (field B d i))

/-- On the engineering grade of the horizon, this is literally the original `Warehouse.qfits` column. -/
theorem top {r:ℕ} (hr:r≤d) (i:B.BIndex (d:ℤ) r):
    column V B d ⟨⟨d,Nat.lt_succ_self d⟩,⟨r,Nat.lt_succ_of_le hr⟩,i⟩=V.qfits B d r i:=rfl

theorem sees (i:Glyph B d):shell V d (column V B d i)=Rune B i:=by
  apply Subtype.ext
  change (observable G d) ((V.scene d).coords.symm (((V.scopeW d).conversion (inftyQ G))
    (((V.scopeW d).conversion (inftyQ G)).symm ((V.scene d).coords (field B d i)))))=Letters B i
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply]
  rfl


def weights : (V.scene d).Coeff →ₗ[ℂ] (Glyph B d → ℂ) :=
  (Daylight B d).equivFun.toLinearMap.comp (shell V d)

/-- The simple gauge group has no equation-ideal component anywhere in the grade-four horizon. -/
theorem faithful (simple : G.Simple) : Injective (shell V 4) := by
  intro x y hxy
  have hs : shell V 4 (x-y)=0 := by rw [map_sub,hxy,sub_self]
  have hi : raw V 4 (x-y) ∈ equationIdeal G 4 := congrArg Subtype.val hs
  have zero := Trace.Terrace.immune4 simple hi
  exact sub_eq_zero.mp ((raw V 4).injective (zero.trans (map_zero _).symm))

/-- Raw coefficient equality on every interacting lattice configuration, before taking any limit. -/
theorem resolution (simple : G.Simple) (x : (V.scene 4).Coeff) :
    x = ∑ i : Glyph B 4, weights V B 4 x i • column V B 4 i := by
  apply faithful V simple
  rw [map_sum]
  simp only [map_smul,sees,←readHeight]
  exact ((Daylight B 4).sum_repr (shell V 4 x)).symm

def fare : ℝ := ∑ i : (V.scene d).Index,∑ q : Glyph B d,‖weights V B d (Pi.single i 1) q‖

/-- One fixed finite coefficient price applies to each actual cutoff, period and submitted label. -/
theorem bounded (c : (V.scene d).Coeff) :
    ∑ q : Glyph B d, ‖weights V B d c q‖ ≤ (V.scene d).coeffSize c * fare V B d := by
  have hc : c = ∑ i : (V.scene d).Index,c i • Pi.single i 1 := by
    ext i
    simp [Pi.single_apply,mul_ite]
  calc
    _ = ∑ q : Glyph B d, ‖∑ i : (V.scene d).Index,c i * weights V B d (Pi.single i 1) q‖ := by
      conv_lhs => rw [hc]
      simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    _ ≤ ∑ q : Glyph B d,∑ i : (V.scene d).Index, ‖c i‖ * ‖weights V B d (Pi.single i 1) q‖ := by
      exact sum_le_sum fun q _ => (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
    _ ≤ _ := by
      rw [sum_comm]
      simp_rw [←mul_sum]
      unfold Frame.coeffSize
      rw [Finset.sum_mul]
      exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (single_le_sum
        (f:=fun h : (V.scene d).Index => ∑ q : Glyph B d, ‖weights V B d (Pi.single h 1) q‖)
        (fun _ _ => sum_nonneg fun _ _ => norm_nonneg _) (mem_univ i)) (norm_nonneg _)

end YM.Integration.WilsonMatrixOriginalIndependentColumns
