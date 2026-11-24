import YM.Integration.WilsonMatrixOriginalIndependentScalar
import YM.Integration.WilsonMatrixOriginalIndependentFields

/-! The sole lower nominal degree has an exactly constant value in the original unmasked Wilson field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalIndependentUnit
open Lattice Wilson RG Precision Source Labels Maxwell MS.Local.Physical MS.Menus MS.Theater
open FVA2 FVA2.Warehouse PhysicalNext.Repeat.Legato WilsonMatrixTicketLanesNativePrices
open WilsonMatrixOriginalIndependentColumns WilsonMatrixOriginalIndependentFields
open scoped Classical BigOperators

variable {G:Gauge} (B:Deck G)

private theorem nonzero (V:Warehouse G) (i:Glyph B 4): field B 4 i≠0:=by
  intro gone
  apply (Daylight B 4).ne_zero i
  have z:WilsonMatrixOriginalIndependentColumns.column V B 4 i=0:=by
    unfold WilsonMatrixOriginalIndependentColumns.column
    rw [gone,map_zero,map_zero]
  rw [readHeight,← sees V B 4 i,z,map_zero]

/-- A nonzero lower glyph exists only in the original bidegree (0,0). -/
theorem degree (V:Warehouse G) (simple:G.Simple) (i:Glyph B 4) (low:i.1.val<4):
    (i.1.val,i.2.1.val)=(0,0):=by
  by_contra wrong
  obtain ⟨c,hc⟩:=UVNext.FreeStress.just_one simple low
    (Warehouse.label B i.1.val i.2.1.val i.2.2)
  have at_zero:=V.fit_ceil B i.2.2 0 (by rw [(V.scene i.1.val).zero_degree]; exact fun eq=>wrong eq.symm)
  change (V.scene i.1.val).coords (Warehouse.label B i.1.val i.2.1.val i.2.2) 0=0 at at_zero
  rw [hc,map_smul,(V.scene i.1.val).coords_unit,Pi.smul_apply] at at_zero
  have vanish:c=0:=by simpa [Frame.e0] using at_zero
  apply nonzero B V i
  unfold field
  rw [hc,vanish,zero_smul,map_zero]

/-- The exact reference field corresponding to a raw unit column, including its true UV spacing. -/
theorem original (C:Family G) (made:C.Makes) (N p:ℕ) (age:C.ref 4≤N):
    (C.factory 4 N p).terminal (C.labels.level 4).e0=(((C.S.a N:ℂ)^4)⁻¹) • C.refUnit 4:=by
  have H:=made.calibrated 4 N p age
  have ht:(C.factory 4 N p).terminal.symm (C.refUnit 4)=unitVec (C.labels.level 4) C.path N:=by
    apply (C.factory 4 N p).terminal.injective
    rw [LinearEquiv.apply_symm_apply,← H.reads,H.unit_coord (C.ref 4) le_rfl age]
  have eq:=congrArg (C.factory 4 N p).terminal ht
  rw [LinearEquiv.apply_symm_apply] at eq
  change C.refUnit 4=(C.factory 4 N p).terminal (((C.S.a N:ℂ)^4) • (C.labels.level 4).e0) at eq
  have a: ((C.S.a N:ℂ)^4)≠0:=pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos N).ne')
  rw [eq,(C.factory 4 N p).terminal.map_smul,smul_smul,inv_mul_cancel₀ a,one_smul]

variable (R:Run G)
/-- All periods, sites and unrestricted group configurations see the same scalar at this cutoff. -/
theorem constant (simple:G.Simple) (i:Glyph B 4) (low:i.1.val<4):
    ∃c:ℂ,∀N p, R.family.ref 4≤N→∀o (U:Config G (R.family.side N p)),
      R.family.O N p (source R B N p i) o U=c*((R.family.S.a N:ℂ)^4)⁻¹:=by
  obtain ⟨c,hc⟩:=WilsonMatrixOriginalIndependentScalar.column B (warehouse R) simple i low
  refine ⟨c,?_⟩
  intro N p age o U
  have q:source R B N p i=(c*((R.family.S.a N:ℂ)^4)⁻¹) • R.family.refUnit 4:=by
    unfold source
    rw [hc]
    change (R.family.factory 4 N p).terminal (c • (R.family.labels.level 4).e0) = _
    rw [(R.family.factory 4 N p).terminal.map_smul,original R.family R.makes N p age,smul_smul]
  rw [q,show R.family.O N p ((c*((R.family.S.a N:ℂ)^4)⁻¹) • R.family.refUnit 4) o=
    (c*((R.family.S.a N:ℂ)^4)⁻¹) • R.family.O N p (R.family.refUnit 4) o from
      (R.family.linearO N p 4 o).map_smul ..,R.family.constant R.makes 4 age o]
  simp

end YM.Integration.WilsonMatrixOriginalIndependentUnit
