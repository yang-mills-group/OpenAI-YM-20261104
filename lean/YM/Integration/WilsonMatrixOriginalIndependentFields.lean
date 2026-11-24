import YM.Integration.WilsonMatrixOriginalIndependentColumns
import YM.Integration.WilsonMatrixTicketLanesCompensatedFields

/-! Independent grade-four sources evaluated on the actual nonlinear Wilson group configuration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalIndependentFields
open Lattice Wilson RG Precision Source Labels MS.Local.Physical MS.Menus FVA2
open Function Finset WilsonMatrixTicketLanesNativePrices WilsonMatrixOriginalIndependentColumns
open PhysicalNext.Repeat.Legato
open scoped BigOperators Classical

variable {G:Gauge} (R:Run G) (B:Deck G) (N p:ℕ)

def source (q:Glyph B 4) : R.family.label 4 :=
  (R.family.factory 4 N p).terminal (column (warehouse R) B 4 q)

def amounts (v:R.family.label 4) : Glyph B 4 → ℂ :=
  weights (warehouse R) B 4 ((R.family.factory 4 N p).terminal.symm v)

theorem prescribed {a:ℕ} (ha:a≤4) (i:B.BIndex (4:ℤ) a) :
    source R B N p ⟨⟨4,by decide⟩,⟨a,Nat.lt_succ_of_le ha⟩,i⟩ =
      WilsonMatrixTicketLanesCompensatedFields.field R B N p 4 a i := rfl

theorem filed (simple:G.Simple) (v:R.family.label 4) :
    v=∑ q:Glyph B 4,amounts R B N p v q • source R B N p q := by
  let t:=(R.family.factory 4 N p).terminal
  calc
    _=t (t.symm v) := (t.apply_symm_apply v).symm
    _=t (∑ q:Glyph B 4,amounts R B N p v q • column (warehouse R) B 4 q) :=
      congrArg t (resolution (warehouse R) B simple _)
    _=_ := (map_sum t _ _).trans (sum_congr rfl (fun q _=>t.map_smul _ _))

/-- The actual bare cylinder as a linear reading of the original unregistered terminal coefficients. -/
def detector (o:Site (R.family.side N p)) (U:Config G (R.family.side N p)) :
    R.family.label 4 →ₗ[ℂ] ℂ :=
  (((R.family.S.a N:ℂ)^4)⁻¹) • (((MvPolynomial.aeval (entry (expandAt o U))).toLinearMap.comp
    (R.family.localSection 4).evalC).comp ((R.family.labels.level 4).scaled (R.family.path.levels.clock.threshold N)⁻¹))

theorem physical (simple:G.Simple) (v:R.family.label 4) (o:Site (R.family.side N p))
    (U:Config G (R.family.side N p)) :
    R.family.O N p v o U = ∑ q:Glyph B 4, amounts R B N p v q * R.family.O N p (source R B N p q) o U := by
  let t:=(R.family.factory 4 N p).terminal
  have value (x:R.family.label 4):R.family.O N p x o U= detector R N p o U (t.symm x):=rfl
  calc
    _ = detector R N p o U (t.symm v) := value v
    _ = detector R N p o U (∑ q:Glyph B 4,amounts R B N p v q • column (warehouse R) B 4 q) :=
      congrArg _ (resolution (warehouse R) B simple _)
    _ = _ := by
      rw [map_sum]
      apply sum_congr rfl; intro q _
      let y:R.family.label 4 := column (warehouse R) B 4 q
      let α := amounts R B N p v q
      have same : R.family.O N p (t y) o U = detector R N p o U y :=
        (value _).trans (congrArg (detector R N p o U) (t.symm_apply_apply y))
      exact ((detector R N p o U).map_smul α y).trans (congrArg (fun z:ℂ=>α*z) same.symm)

/-- The joint word, with each of its original signed means retained, at arbitrary addressed sites. -/
theorem centered (simple:G.Simple) {I:Type} [Fintype I] (v:I→R.family.label 4)
    (c:I→ℂ) (o:I→Site (R.family.side N p)) (U:Config G (R.family.side N p)) :
    (∏i,(R.family.O N p (v i) (o i) U-c i))=
      ∏i,((∑ q:Glyph B 4,amounts R B N p (v i) q * R.family.O N p (source R B N p q) (o i) U)-c i) := by
  apply prod_congr rfl; intro i _; rw [physical R B N p simple (v i)]

end YM.Integration.WilsonMatrixOriginalIndependentFields
