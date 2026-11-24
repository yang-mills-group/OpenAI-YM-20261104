import YM.Integration.WilsonMatrixOriginalDeckRawComparison
import YM.Integration.WilsonMatrixOriginalDeckEdgeIncome

/-! The dressed independent self and mixed matrices and their exact signed remainder on each original scale pair. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckRawAssay
open Filter Set Finset MeasureTheory Spec Table Ward PhysMS RG17 Lattice Wilson RG MS MS.Menus MS.Local.Physical
open Extraction Extraction.Order PhysicalNext.Repeat.Legato Next.UVStress Push.GridApprox OPE OPE.Therm
open WilsonMatrixOriginalDeckRawMoment WilsonMatrixOriginalDeckRawComparison WilsonMatrixOriginalDeckFiledDebit
open WilsonMatrixOriginalDeckRelative WilsonMatrixOriginalDeckError
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book} (F:Spec.Final R.family f S) (L:Layout F)
variable {D:Deck G} (Q:MS.Land.Prescription D) (h:ℕ)
local notation "I"=> Glyph D h

/-- The complete row is kept for each proposed degree and each chosen coefficient. -/
structure Roster (D:Deck G) (h:ℕ) where
  weights : Glyph D h→Glyph D h→ℂ
  clock : Glyph D h→ℝ
  order : Glyph D h→ℕ

def matrix (T:Test 2)(z:ℕ×ℕ) (a b:Roster D h):Matrix I I ℂ:=fun i j=>
  let ν:=scene R.family.path z.1 z.2 z.1
  let X:=WilsonMatrixOriginalDeckRawPanel.registered R Q h z.1 z.2 (a.weights i) (a.clock i) (a.order i)
  let Y:=WilsonMatrixOriginalDeckRawPanel.registered R Q h z.1 z.2 (b.weights j) (b.clock j) (b.order j)
  WilsonMatrixOriginalDeckRawGrid.observed R Q h T z.1 z.2 ν (a.weights i) (b.weights j) (a.clock i) (b.clock j) (a.order i) (b.order j)+
    separatedMeans R T z.1 z.2 ν X Y

def signed (T:Test 2)(z:ℕ×ℕ)(r s:ℝ)(w v:I→R.family.label h)(a b:Roster D h):Matrix I I ℂ:=fun i j=>
  due R T (scene R.family.path z.1 z.2 z.1) (deposited R F L h r (w i) z.1 z.2) (deposited R F L h s (v j) z.1 z.2)
    (WilsonMatrixOriginalDeckRawPanel.registered R Q h z.1 z.2 (a.weights i) (a.clock i) (a.order i))
    (WilsonMatrixOriginalDeckRawPanel.registered R Q h z.1 z.2 (b.weights j) (b.clock j) (b.order j))

theorem fields (g:Test 2){r:ℝ}(hr:0<r)(s:ℝ)(w v:I→R.family.label h)(a b:Roster D h)(z:ℕ×ℕ):
    field R D F L h g hr s w v z=matrix R Q h (dilate hr g) z a b+signed R F L Q h (dilate hr g) z r s w v a b:=by
  ext i j
  have c:=(WilsonMatrixOriginalDeckRawComparison.measured R F L h Q g hr s (w i) (v j) z
    (a.weights i) (b.weights j) (a.clock i) (b.clock j) (a.order i) (b.order j)).1
  exact (sub_eq_iff_eq_add.mp c).trans (add_comm _ _)

/-- One stock trial across the full before-regulator matrix. The same-date error is multiplied by its entire signed candidate. -/
theorem booked (g:Test 2)(r:ℕ→ℝ)(pos:∀i,0<r i)(w:ℕ→I→R.family.label h)(a:ℕ→Roster D h)
    (V:ℕ→Matrix I I ℂ)(i:ℕ)(z:ℕ×ℕ):
    let T:=dilate (pos (i+1)) g
    let C:=matrix R Q h T z (a (i+1)) (a i)
    let G₀:=matrix R Q h T z (a (i+1)) (a (i+1))
    let E:=signed R F L Q h T z (r (i+1)) (r i) (w (i+1)) (w i) (a (i+1)) (a i)
    let H:=signed R F L Q h T z (r (i+1)) (r (i+1)) (w (i+1)) (w (i+1)) (a (i+1)) (a (i+1))
    WilsonMatrixOriginalDeckEdgeIncome.cost R D F L h g r pos w V i z = amount ((C-G₀*V i)+(E-H*V i)) ∧
      WilsonMatrixOriginalDeckEdgeIncome.cost R D F L h g r pos w V i z ≤ amount (C-G₀*V i)+amount E+amount H*amount (V i):=by
  dsimp only;unfold WilsonMatrixOriginalDeckEdgeIncome.cost
  rw [fields R F L Q h g (pos (i+1)) (r i) (w (i+1)) (w i) (a (i+1)) (a i) z,
    fields R F L Q h g (pos (i+1)) (r (i+1)) (w (i+1)) (w (i+1)) (a (i+1)) (a (i+1)) z]
  generalize matrix R Q h (dilate (pos (i+1)) g) z (a (i+1)) (a i)=C
  generalize matrix R Q h (dilate (pos (i+1)) g) z (a (i+1)) (a (i+1))=G₀
  generalize signed R F L Q h (dilate (pos (i+1)) g) z (r (i+1)) (r i) (w (i+1)) (w i) (a (i+1)) (a i)=E
  generalize signed R F L Q h (dilate (pos (i+1)) g) z (r (i+1)) (r (i+1)) (w (i+1)) (w (i+1)) (a (i+1)) (a (i+1))=H
  have split:C+E-(G₀+H)*V i=(C-G₀*V i)+(E-H*V i):=by rw [add_mul];abel
  rw [split];refine ⟨rfl,?_⟩
  have neg (X:Matrix I I ℂ):amount (-X)=amount X:=by simp [WilsonMatrixOriginalDeckRelative.amount]
  calc amount ((C-G₀*V i)+(E-H*V i)) ≤ amount (C-G₀*V i)+amount (E-H*V i):=add_cost _ _
       _ ≤ amount (C-G₀*V i)+(amount E+amount (H*V i)):=by
         apply add_le_add_right;rw [sub_eq_add_neg];exact (add_cost E (-(H*V i))).trans_eq (by rw [neg])
       _ ≤ amount (C-G₀*V i)+amount E+amount H*amount (V i):=by rw [←add_assoc];exact add_le_add_right (product_cost H (V i)) _

end YM.Integration.WilsonMatrixOriginalDeckRawAssay
