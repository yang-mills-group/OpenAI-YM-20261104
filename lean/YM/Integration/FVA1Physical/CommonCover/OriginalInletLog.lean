import YM.Integration.FVA1Physical.CommonCover.OriginalOlderPrice
import YM.Comparison.RG02.Actual.Mask
import YM.Integration.FVA1Physical.Round2.CP5WilsonExponent

/-! Original marked-inlet and vacuum charges, using a single census and
all its mixed sectors on the physical no-flag window. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.OlderPrice
open MeasureTheory Filter Function Finset RG Wilson Gauge Precision Tree Lattice Exterior
open Comparison.RG02 Order Marker Multi Integral Actual Push.SectorMeasure
open Extra.Trajectories (connected)
open scoped Classical

variable {I : Type} [DecidableEq I] [Fintype I] {R : Census I}

omit [Fintype I] in
theorem tagged_center_price (D M Q : Poly R) (w : I→ℝ) (hw : ∀i,0<w i)
    {a b k : ℝ} (ha : 0<a) (hb : 0<b) (hk : 0≤k)
    (da : D.part R.quiet=(a:ℂ)) (mb : M.part R.quiet=(b:ℂ)) :
    let Z := (k:ℂ) • (D-M)
    Poly.price w (Z-Z.part R.quiet • Q) ≤
      k*(a*Poly.price w (unitScale D-unitScale M)+
        max a b * |Real.log a-Real.log b| * Poly.price w (unitScale M-Q)) := by
  intro Z
  have scale (v : ℝ) (hv : 0<v) (P : Poly R) (h : P.part R.quiet=(v:ℂ)) :
      (v:ℂ) • unitScale P=P := h ▸ scale_value (h ▸ Complex.ofReal_ne_zero.mpr hv.ne')
  have id : Z-Z.part R.quiet • Q = (k:ℂ) •
      ((a:ℂ) • (unitScale D-unitScale M)+((a-b:ℝ):ℂ) • (unitScale M-Q)) := by
    ext s
    have one (v : ℝ) (hv : 0<v) (P : Poly R) (h : P.part R.quiet=(v:ℂ)) :
        (v:ℂ)*(unitScale P).part s=P.part s := congrArg (Poly.part · s) (scale v hv P h)
    simp only [Z, Extra.Trajectories.part_sub,Poly.part_smul,Poly.part_plus,da,mb,Complex.ofReal_sub]
    rw [←one a ha D da,←one b hb M mb]
    ring
  rw [id,Poly.adapted,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hk]
  apply mul_le_mul_of_nonneg_left _ hk
  apply (Poly.addition hw _ _).trans
  simp only [Poly.adapted,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha]
  exact add_le_add_right (mul_le_mul_of_nonneg_right (mass_change ha hb)
    (Poly.nonnegative hw _)) _

variable {G : Gauge} {c f : Side} {S : StepData c f} {P : Rep G f} {O : ChartRatio G}
  (K : Bulk.Kernel S P.clip P.path O) (W : Bulk.Colors R G f)
  (D : Lit R (Config G f)) (g : ℝ) (w : I→ℝ)

omit [Fintype I] in
/-- The physical error is the admitted activity mismatch in the quiet
sector. The extensive scalar and the two physical background actions cancel. -/
theorem calm_vacuum_change (U : Config G f) (heat : P.beta=temperature g) (calm : U∈Calm P.p) :
    Real.log (P.eval U) - Real.log (weight g (levelScalar P) U W P.clip P.path) =
      -remainderVac W U g P := by
  have pos : 0 < weight g (levelScalar P) U W P.clip P.path := Real.exp_pos _
  rw [base_entry W g heat calm, Real.log_mul pos.ne' (Real.exp_pos _).ne',Real.log_exp]
  ring

def mixedBill (U : Config G f) : ℝ :=
  ∑ s ∈ univ.erase R.quiet, Poly.toll w s * ‖(errorLog D W U g P).part s‖

/-- The independent model is charged against **all** incoming marked
log coefficients in the same original norm, with its own exact normalization. -/
theorem calm_mixed_change (floor : Floor P D) (hw : ∀i,0<w i) (U : Config G f) (calm : U∈Calm P.p) :
    Poly.price w (unitScale (D U) - unitScale (model g (levelScalar P) W K U)) ≤
      Real.exp (Poly.price w (markedLog g U W))*(Real.exp (mixedBill (P:=P) W D g w U)-1) := by
  let L := markedLog g U W
  let X := unitScale (D U)
  have xquiet : X.part R.quiet=1 :=
    unitScore ((floor.vacancy U) ▸ Complex.ofReal_ne_zero.mpr (healthy_live calm).ne')
  have marked : connected X=markWeight P D U := by
    change connected (((D U).part R.quiet)⁻¹ • D U)=_
    rw [floor.vacancy]
    rfl
  have logzero : L.part R.quiet=0 := part_lit_quiet _
  have tab : Round2.CP5.wilsonLogTable R L.part=L := by
    ext s
    change (if s=R.quiet then 0 else L.part s)=L.part s
    split <;> rename_i h
    · exact h ▸ logzero.symm
    · rfl
  let cost := fun s:R.Mode=>Poly.toll w s*‖(errorLog D W U g P).part s‖
  have price := Round2.CP5.wilson_density_error w hw X xquiet L.part cost (fun s _=> by
    change Poly.toll w s * ‖(connected X).part s-L.part s‖ ≤
      Poly.toll w s * ‖(markWeight P D U-markedLog g U W).part s‖
    rw [marked, Extra.Trajectories.part_sub])
  have model_eq : unitScale (model g (levelScalar P) W K U)=Poly.pass L := by
    have pos : 0<weight g (levelScalar P) U W P.clip P.path := Real.exp_pos _
    unfold unitScale
    rw [model_unit,model,smul_smul,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr pos.ne'),one_smul]
  rw [model_eq]
  simpa only [tab,X,L,cost,mixedBill] using price.2.2.2

end YM.Integration.FVA1Physical.OlderPrice
