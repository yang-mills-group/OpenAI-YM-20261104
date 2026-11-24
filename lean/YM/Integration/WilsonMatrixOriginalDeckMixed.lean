import YM.Integration.WilsonMatrixOriginalDeckInverse

/-! The two physical insertion dates are read on the same separated test at the reporting radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckMixed
open Matrix Function Filter Set MeasureTheory Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open Extraction Table Spec Climb FVA2 FVA2.ColorCode OPE OPE.Orbits OPE.Levy RG11.Fields
open scoped Classical Topology BigOperators Matrix
open private regular from YM.Integration.WilsonMatrixOriginalDeckGram

private def second {E:Type*} [AddCommGroup E] [Module ℂ E] (P:MultilinearMap ℂ (fun _:Fin 2=>E) ℂ) (a:E) : E→ₗ[ℂ]ℂ :=
  P.toLinearMap ![a,0] 1

private theorem at_second {E:Type*} [AddCommGroup E] [Module ℂ E] (P:MultilinearMap ℂ (fun _:Fin 2=>E) ℂ) (a b:E) :
    second P a b=P ![a,b] := by
  rw [second,P.toLinearMap_apply]
  exact congrArg _ (funext fun i=>by fin_cases i <;> simp [Function.update])

variable {G:Gauge} {C:Family G} {S:Table C.book} {f:Extraction.Order}
variable (B:Deck G) (F:Spec.Final C f S) (J:ℝ→PhysMS.tower S) (h:ℕ)

/-- Coordinates of the true change from the second date to the measuring date, on the whole horizon. -/
def change (r s:ℝ) : Matrix (Glyph B h) (Glyph B h) ℂ := fun j b=>
  (WilsonMatrixOriginalDeckColumns.basis C B h).repr
    ((J r h).symm (J s h (WilsonMatrixOriginalDeckColumns.basis C B h b))) j

/-- Evaluate both actual hierarchy fields at the same two positions, normalized at r and s respectively. -/
def paired (r s:ℝ) (a b:Glyph B h) (x:Points 2) : ℂ :=
  S.classMoment S (fun _:Fin 2=>h) (r•x)
    ![J r h (WilsonMatrixOriginalDeckColumns.basis C B h a),J s h (WilsonMatrixOriginalDeckColumns.basis C B h b)]

def mixed (g:Test 2) (r s:ℝ) : Matrix (Glyph B h) (Glyph B h) ℂ := fun a b=>g.applyTo (paired B J h r s a b)

theorem filed (r s:ℝ) (b:Glyph B h) :
    ∑j,change B J h r s j b • J r h (WilsonMatrixOriginalDeckColumns.basis C B h j) =
      J s h (WilsonMatrixOriginalDeckColumns.basis C B h b) := by
  let E := WilsonMatrixOriginalDeckColumns.basis C B h
  change (∑j,E.repr ((J r h).symm (J s h (E b))) j • J r h (E j)) = _
  have hsum := congrArg (fun z=>J r h z) (E.sum_repr ((J r h).symm (J s h (E b))))
  simpa only [map_sum,map_smul,LinearEquiv.apply_symm_apply] using hsum

theorem mark (r s:ℝ) (a b:Glyph B h) (x:Points 2) :
    paired B J h r s a b x = ∑j,change B J h r s j b * paired B J h r r a j x := by
  let P := S.classMoment S (fun _:Fin 2=>h) (r•x)
  let A := J r h (WilsonMatrixOriginalDeckColumns.basis C B h a)
  change P ![A,J s h (WilsonMatrixOriginalDeckColumns.basis C B h b)] = _
  rw [←at_second,←filed B J h r s b,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul,at_second]
  rfl

private theorem diagonal (r:ℝ) (a b:Glyph B h) : paired B J h r r a b =
    PhysMS.measured F none (J r) (d:=fun _:Fin 2=>h)
      (WilsonMatrixOriginalDeckColumns.basis C B h ∘ ![a,b]) r := by
  funext x
  unfold paired PhysMS.measured
  apply congrArg _
  ext i
  fin_cases i <;> rfl

/-- Exact signed mixed matrix. No estimate, inversion, or deletion of lower fields enters this identity. -/
theorem observed (g:Test 2) {r:ℝ} (hr:0<r) (s:ℝ) :
    mixed B J h g r s = WilsonMatrixOriginalDeckGram.bank B F J h g r * change B J h r s := by
  classical
  ext a b
  let c := fun j=>change B J h r s j b
  let E := fun j=>paired B J h r r a j
  change g.applyTo (paired B J h r s a b) = _
  have exactField : paired B J h r s a b = fun x=>∑j,c j*E j x := funext fun x=>mark B J h r s a b x
  rw [exactField]
  have cont (j:Glyph B h) (x:Points 2) (hx:x∈tsupport g) : ContinuousAt (fun z=>c j*E j z) x := by
    apply continuousAt_const.mul
    dsimp [E]
    rw [diagonal B F J h]
    exact (regular B F J a j hr x (g.tsupport_subset hx)).continuousAt ((conf_open _).mem_nhds (g.tsupport_subset hx))
  rw [OPETreeTests.sum g Finset.univ (fun j x=>c j*E j x) (fun j _ x hx=>cont j x hx)]
  change (∑j,g.applyTo (fun x=>c j*E j x)) = ∑j,WilsonMatrixOriginalDeckGram.bank B F J h g r a j * c j
  apply Finset.sum_congr rfl
  intro j _
  rw [OPETreeTests.scalar,mul_comm]
  dsimp [E,WilsonMatrixOriginalDeckGram.bank]
  rw [diagonal B F J h]

end YM.Integration.WilsonMatrixOriginalDeckMixed
