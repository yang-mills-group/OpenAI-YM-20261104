import YM.Integration.WilsonMacroscopicRichMeasuredGram

/-! Each column of the independent smooth rich MS bank is a literal original
RG17 exterior. The physical radius rescales the entire test, including its
Jacobian; the translation of the two sites is the original Ward identity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichRegister
open Function Matrix Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open Extraction Table Spec Climb Filter Set Finset PhysMS MeasureTheory Next.UVStress
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} (B : Deck G)
variable (F : Spec.Final C f S) (J : ℝ→PhysMS.tower S) {h : ℕ}

def exterior (g : Test 2) {τ : ℝ} (pos : 0<τ) (b : Glyph B h) : RG17.External C S where
  n := 1
  tags := fun _=>⟨h,J τ h (WilsonMacroscopicRichFree.basis C B h b)⟩
  test := Next.UVStress.dilate pos g

theorem column (g : Test 2) {τ : ℝ} (pos : 0<τ) (a b : Glyph B h) :
    (exterior B J g pos b).charge F h (J τ h (WilsonMacroscopicRichFree.basis C B h a)) =
      WilsonMacroscopicRichMeasuredGram.bank B F J h g τ a b := by
  let X := exterior B J g pos b
  let v := J τ h (WilsonMacroscopicRichFree.basis C B h a)
  let u (i : Fin 2) := J τ h (WilsonMacroscopicRichFree.basis C B h (![a,b] i))
  change (Next.UVStress.dilate pos g).applyTo (X.pay h v)=g.applyTo (PhysMS.measured F none (J τ) (d:=fun _ : Fin 2=>h) (WilsonMacroscopicRichFree.basis C B h ∘ ![a,b]) τ)
  rw [Next.UVStress.zoom_integral]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z∈tsupport g
  · have native := X.pay_eq F h v (τ • z) (Work.A05.smul_conf pos (g.tsupport_subset hz))
    have tags : Fin.cons (α:=fun _ : Fin 2=>S.Tag) ⟨h,v⟩ X.tags=fun i=>⟨h,u i⟩ := by
      funext i;fin_cases i <;> rfl
    exact congrArg (g z * ·) (native.trans (congrArg (S.useAt S (τ • z)) tags))
  · simp [image_eq_zero_of_notMem_tsupport hz]

def coords {τ : ℝ} (p : S.Field h) : Glyph B h→ℂ :=
  (WilsonMacroscopicRichFree.basis C B h).equivFun ((J τ h).symm p)

theorem read_field (g : Test 2) {τ : ℝ} (pos : 0<τ) (b : Glyph B h) (p : S.Field h) :
    (exterior B J g pos b).charge F h p = (WilsonMacroscopicRichMeasuredGram.bank B F J h g τ).vecMul (coords B J (τ:=τ) p) b := by
  let e := WilsonMacroscopicRichFree.basis C B h
  let v := (J τ h).symm p
  let X := exterior B J g pos b
  calc
    X.charge F h p = X.charge F h (J τ h (∑ i : Glyph B h,e.equivFun v i • e i)) := by rw [e.sum_equivFun,LinearEquiv.apply_symm_apply]
    _ = ∑ i : Glyph B h,e.equivFun v i*WilsonMacroscopicRichMeasuredGram.bank B F J h g τ i b := by
      simp only [map_sum,map_smul,smul_eq_mul]
      apply sum_congr rfl;intro i _
      exact congrArg (e.equivFun v i* ·) (column B F J g pos i b)
    _ = _ := rfl

end YM.Integration.WilsonMacroscopicRichRegister
