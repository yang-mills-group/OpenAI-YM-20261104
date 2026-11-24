import YM.Integration.WilsonMatrixOriginalDeckReturn
import YM.Integration.WilsonMatrixOriginalDeckRelative

/-! The full signed exterior reading of an arbitrary high-to-low trial in the measured frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckExterior
open Filter Finset MeasureTheory Pert Pert.Position MS MS.Menus MS.Local.Physical MS.Land MS.Theater
open Extraction Extraction.Order Spec Climb FVA2 FVA2.ColorCode OPE OPE.Orbits OPE.Levy RG11.Fields
open Trace.Pilot Table PhysMS RG17 SharpGram SharpGram.Lenses
open WilsonMatrixOriginalDeckColumns WilsonMatrixOriginalDeckMixed WilsonMatrixOriginalDeckRelative
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} {C:Family G} {S:Table C.book}
variable (B:Deck G) (J:ℝ→PhysMS.tower S) (h:ℕ)

/-- The expense of this particular complex-linear outer measurement on the full basis. -/
def fare (t:ℝ) (E:S.Field h→ₗ[ℂ]ℂ) : ℝ := ∑j:Glyph B h,‖E (J t h (WilsonMatrixOriginalDeckColumns.basis C B h j))‖

def proposed (t:ℝ) (E:S.Field h→ₗ[ℂ]ℂ) (V:Matrix (Glyph B h) (Glyph B h) ℂ) (b:Glyph B h) : ℂ :=
  ∑j,V j b*E (J t h (WilsonMatrixOriginalDeckColumns.basis C B h j))

/-- The genuine outer observation evaluates the complete change of coordinates. -/
theorem trueValue (t s:ℝ) (E:S.Field h→ₗ[ℂ]ℂ) (b:Glyph B h) :
    E (J s h (WilsonMatrixOriginalDeckColumns.basis C B h b)) = proposed B J h t E (change B J h t s) b := by
  rw [←filed B J h t s b,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  rfl

/-- Signed error of one whole high column at the given outer physical observer. -/
theorem error (t s:ℝ) (E:S.Field h→ₗ[ℂ]ℂ) (V:Matrix (Glyph B h) (Glyph B h) ℂ) (b:Glyph B h) :
    ‖proposed B J h t E V b-E (J s h (WilsonMatrixOriginalDeckColumns.basis C B h b))‖≤fare B J h t E*amount (V-change B J h t s) := by
  classical
  rw [trueValue B J h t s E b]
  let D:=V-change B J h t s
  have term (j:Glyph B h) : ‖E (J t h (WilsonMatrixOriginalDeckColumns.basis C B h j))‖≤fare B J h t E :=
    Finset.single_le_sum (fun i _=>norm_nonneg (E (J t h (WilsonMatrixOriginalDeckColumns.basis C B h i)))) (Finset.mem_univ _)
  have col : (∑j,‖D j b‖)≤amount D := Finset.sum_le_sum fun j _=>
    Finset.single_le_sum (fun i _=>norm_nonneg (D j i)) (Finset.mem_univ _)
  have diff : proposed B J h t E V b-proposed B J h t E (change B J h t s) b=
      ∑j,D j b*E (J t h (WilsonMatrixOriginalDeckColumns.basis C B h j)) := by
    unfold proposed
    rw [←Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _=>(sub_mul _ _ _).symm
  calc
    _=‖∑j,D j b*E (J t h (WilsonMatrixOriginalDeckColumns.basis C B h j))‖:=congrArg norm diff
    _≤∑j,‖D j b*E (J t h (WilsonMatrixOriginalDeckColumns.basis C B h j))‖:=norm_sum_le _ _
    _≤∑j,‖D j b‖*fare B J h t E:=Finset.sum_le_sum fun j _=>by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (term j) (norm_nonneg _)
    _=(∑j,‖D j b‖)*fare B J h t E:=(Finset.sum_mul ..).symm
    _≤amount D*fare B J h t E:=mul_le_mul_of_nonneg_right col (Finset.sum_nonneg fun _ _=>norm_nonneg _)
    _=fare B J h t E*amount D:=mul_comm _ _

/-- The signed coefficients of a whole incoming high sector are summed before taking the observed error. -/
theorem weighted (t s:ℝ) (E:S.Field h→ₗ[ℂ]ℂ) (V:Matrix (Glyph B h) (Glyph B h) ℂ) (c:Glyph B h→ℂ) :
    ‖(∑b,c b*proposed B J h t E V b)-∑b,c b*E (J s h (WilsonMatrixOriginalDeckColumns.basis C B h b))‖≤
      (∑b,‖c b‖)*(fare B J h t E*amount (V-change B J h t s)) := by
  rw [←Finset.sum_sub_distrib,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left (error B J h t s E V b) (norm_nonneg _)

end YM.Integration.WilsonMatrixOriginalDeckExterior
