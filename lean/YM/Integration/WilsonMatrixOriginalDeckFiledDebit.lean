import YM.Integration.WilsonMatrixOriginalDeckFiled

/-! Signed error measured directly with the funded atRef fields over all pairs of deck glyphs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckFiledDebit
open Filter Set Finset MeasureTheory Pert Pert.Position MS MS.Menus MS.Local.Physical MS.Land MS.Theater
open Extraction Extraction.Order Spec Climb FVA2 FVA2.ColorCode OPE OPE.Orbits OPE.Levy RG11.Fields
open RG17 Next.UVStress Push.GridApprox PhysicalNext.Repeat.Legato WilsonMatrixOriginalDeckMixed
open WilsonMatrixOriginalDeckFiled WilsonMatrixOriginalDeckRelative WilsonMatrixOriginalDeckSignedMeasurements
open private identity from YM.Integration.WilsonMatrixOriginalDeckCutoff
open private continuous_cost from YM.Integration.WilsonMatrixOriginalDeckSignedMeasurements
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} (R:Run G) (B:Deck G) {f:Extraction.Order} {S:Table R.family.book}
variable (F:Spec.Final R.family f S) (L:Layout F) (J:ℝ→PhysMS.tower S) (h:ℕ)

/-- Each column pair uses both already chosen full finite lattice labels with all of their older corrections. -/
def field (g:Test 2) {r:ℝ} (hr:0<r) (s:ℝ) (w v:Glyph B h→R.family.label h) (z:ℕ×ℕ) : Matrix (Glyph B h) (Glyph B h) ℂ :=
  fun a b=>operand R F L h g hr s (w a) (v b) z

/-- One actual original two-point measurement for every entry of the proposed comparison. -/
def debit (g:Test 2) (r:ℕ→ℝ) (pos:∀i,0<r i) (w:ℕ→Glyph B h→R.family.label h)
    (V:ℕ→Matrix (Glyph B h) (Glyph B h) ℂ) (n:ℕ) (z:ℕ×ℕ) : ℝ :=
  ∑i∈range n,amount (field R B F L h g (pos (i+1)) (r i) (w (i+1)) (w i) z-
    field R B F L h g (pos (i+1)) (r (i+1)) (w (i+1)) (w (i+1)) z*V i)

theorem realized (g:Test 2) (r:ℕ→ℝ) (pos:∀i,0<r i) (w:ℕ→Glyph B h→R.family.label h)
    (V:ℕ→Matrix (Glyph B h) (Glyph B h) ℂ) (n:ℕ)
    (age:∀i≤n,R.family.ref h≤L.level (r i))
    (filed:∀i≤n,∀a,master L h (r i) (w i a)=J (r i) h (WilsonMatrixOriginalDeckColumns.basis R.family B h a))
    (u:Filter (ℕ×ℕ)) [u.NeBot] (cut:u≤L.lens) :
    Tendsto (debit R B F L h g r pos w V n) u (𝓝 (WilsonMatrixOriginalDeckSignedMeasurements.invoice R B F J h g r V n)) := by
  have entry (i j:ℕ) (hi:i≤n) (hj:j≤n) :
      Tendsto (field R B F L h g (pos i) (r j) (w i) (w j)) u (𝓝 (mixed B J h g (r i) (r j))) := by
    apply tendsto_pi_nhds.mpr
    intro a
    apply tendsto_pi_nhds.mpr
    intro b
    exact issued R B F L J h g (pos i) (age i hi) (age j hj) a b (w i a) (w j b) (filed i hi a) (filed j hj b) u cut
  apply tendsto_finsetSum
  intro i hi
  have next : i+1≤n := mem_range.mp hi
  have cross := entry (i+1) i next (Nat.le_of_succ_le next)
  have diag := entry (i+1) (i+1) next next
  rw [WilsonMatrixOriginalDeckMixed.observed B F J h g (pos (i+1)),identity R B J h,mul_one] at diag
  exact continuous_cost.continuousAt.tendsto.comp (cross.sub (diag.mul tendsto_const_nhds))

end YM.Integration.WilsonMatrixOriginalDeckFiledDebit
