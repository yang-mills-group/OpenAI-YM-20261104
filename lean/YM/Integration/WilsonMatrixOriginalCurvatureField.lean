import YM.Integration.WilsonMatrixOriginalCurvatureStock

/-! The complete finite physical curvature reading and its original uncorrected dictionary cylinder. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalCurvatureField
open Lattice Wilson RG Precision Source Labels Maxwell StressFlux MS.Local.Physical MS.Menus MS.Theater
open UVNext.FreeStress FVA2 FVA2.Warehouse Finset PhysicalNext.Repeat.Legato
open WilsonMatrixOriginalIndependentFields WilsonMatrixOriginalCurvatureStock
open WilsonMatrixTicketLanesNativePrices WilsonMatrixOriginalIndependentColumns
open private tape_degree from YM.Integration.WilsonReportingPrescribedOldAction
open scoped Classical BigOperators

variable {G:Gauge}

private theorem slotted (F:Labels.Frame G 4) (simple:G.Simple) (j:F.Index) (live:j≠0):
    F.grades j=(4,2):=by
  by_contra no
  have active:F.grades j≠(0,0):=by
    intro h
    have pos:=F.factors_pos j live
    rw [h] at pos
    exact (lt_irrefl 0) pos
  obtain ⟨c,v,parts⟩:=span_four simple (F.basis j)
  have hb (a b:Place 0):Labels.gradePart (F.grades j) (bond (G:=G) a b (d:=4) le_rfl)=0:=
    Labels.gradePart_zero _ _ (4,2) no (tape_degree a b)
  have hu:=Labels.gradePart_zero (Labels.unit G 4) (F.grades j) (0,0) active (Labels.unit_grade 4)
  have removed:=congrArg (Labels.gradePart (G:=G) (d:=4) (F.grades j)) parts
  simp only [Labels.gradePart_self (F.basis j) _ (F.pure j),map_add,map_sum,map_smul,hb,hu,smul_zero,
    Finset.sum_const_zero,zero_add] at removed
  exact F.basis.ne_zero j removed

/-- Infinite Wick subtraction on an actual two-curvature source changes only its gauge-independent vacuum. -/
theorem corrected (V:Warehouse G) (B:Deck G) (simple:G.Simple) (i:B.BIndex (4:ℤ) 2):
    ∃c:ℂ,V.qfits B 4 2 i=V.fits B 4 2 i+c • (V.scene 4).e0:=by
  refine ⟨V.qfits B 4 2 i 0-V.fits B 4 2 i 0,?_⟩
  ext j
  by_cases h:j=0
  · subst j
    simp [Labels.Frame.e0]
  · have keep:2≤V.grade 4 j:=by
      change 2≤((V.scene 4).grades j).2
      rw [slotted _ simple j h]
    simp [Pi.smul_apply,Labels.Frame.e0,Pi.single_eq_of_ne h,V.aligns B i j keep]

private theorem scale {E:Type*} [AddCommGroup E] [Module ℂ E] (M:E→ₗ[ℂ] ℂ) (a b:ℂ) (x:E):
    a*M (b • x)=a*b*M x:=by rw [map_smul,smul_eq_mul,mul_assoc]

private theorem addScalar {E:Type*} [AddCommGroup E] [Module ℂ E] (M:E→ₗ[ℂ] ℂ)
    (x y u:E) (c:ℂ) (eq:x=y+c • u):M x=M y+c*M u:=by rw [eq,map_add,map_smul,smul_eq_mul]

variable (R:Run G) (B:Deck G)
local notation "V" => warehouse R

def normalization (N:ℕ):ℂ:=((R.family.S.a N:ℂ)^4)⁻¹*(((R.family.path.levels.clock.threshold N)⁻¹^2:ℝ):ℂ)

private theorem fee (N p:ℕ) (o:Site (R.family.side N p)) (U:Config G (R.family.side N p))
    (i:B.BIndex (4:ℤ) 2):
    detector R N p o U ((warehouse R).fits B 4 2 i)=normalization R N*
      (((ActualOriginalDictionary.dictionary R B).cylinder 4 2 i).O _ o U:ℂ):=by
  rw [ActualOriginalDictionary.original_section]
  let a:=(((R.family.S.a N:ℂ)^4)⁻¹)
  let t:=(R.family.path.levels.clock.threshold N)⁻¹
  let M:R.family.label 4→ₗ[ℂ] ℂ:=(MvPolynomial.aeval (entry (expandAt o U))).toLinearMap.comp
    (R.family.localSection 4).evalC
  change a*M ((R.family.labels.level 4).scaled t ((warehouse R).fits B 4 2 i))=a*(t^2:ℝ)*M ((warehouse R).fits B 4 2 i)
  have grad:(R.family.labels.level 4).scaled t ((warehouse R).fits B 4 2 i)=(↑(t^2:ℝ):ℂ) • (warehouse R).fits B 4 2 i:=
    (R.family.labels.level 4).scaled_pure t (4,2) (Warehouse.label_grade B i)
  exact (congrArg (fun z:R.family.label 4=>a*M z) grad).trans (scale M a ((t^2:ℝ):ℂ) _)

private theorem registered (N p:ℕ) (o:Site (R.family.side N p)) (U:Config G (R.family.side N p))
    (x:R.family.label 4):
    R.family.O N p ((R.family.factory 4 N p).terminal x) o U=detector R N p o U x:=by
  change detector R N p o U ((R.family.factory 4 N p).terminal.symm ((R.family.factory 4 N p).terminal x))=_
  rw [LinearEquiv.symm_apply_apply]

/-- At every original period the same constant is the entire discrepancy. Both measured scaling
factors multiply the original curvature cylinder, before a gauge field or a site is specified. -/
theorem measured (simple:G.Simple) (i:B.BIndex (4:ℤ) 2):
    ∃c:ℂ,∀N p,R.family.ref 4≤N→∀o(U:Config G (R.family.side N p)),
      R.family.O N p (source R B N p (curvature B i)) o U=
        normalization R N*(((ActualOriginalDictionary.dictionary R B).cylinder 4 2 i).O _ o U:ℂ)+
          c*(((R.family.S.a N:ℂ)^4)⁻¹):=by
  obtain ⟨c,hc⟩:=corrected V B simple i
  refine ⟨c,?_⟩
  intro N p age o U
  change R.family.O N p ((R.family.factory 4 N p).terminal ((warehouse R).qfits B 4 2 i)) o U=_
  have vac:=WilsonMatrixOriginalIndependentUnit.original R.family R.makes N p age
  have z:detector R N p o U (R.family.labels.level 4).e0=(((R.family.S.a N:ℂ)^4)⁻¹):=by
    rw [←registered,vac]
    have lin:=congrFun ((R.family.linearO N p 4 o).map_smul (((R.family.S.a N:ℂ)^4)⁻¹) (R.family.refUnit 4)) U
    change R.family.O N p _ o U=_
    rw [show R.family.O N p ((((R.family.S.a N:ℂ)^4)⁻¹) • R.family.refUnit 4) o U=
      ((R.family.S.a N:ℂ)^4)⁻¹*R.family.O N p (R.family.refUnit 4) o U from lin,
      R.family.constant R.makes 4 age o]
    simp
  exact (registered R N p o U _).trans ((addScalar (detector R N p o U) _ _ _ c hc).trans
    (congrArg₂ (·+·) (fee R B N p o U i) (congrArg (c*·) z)))

end YM.Integration.WilsonMatrixOriginalCurvatureField
