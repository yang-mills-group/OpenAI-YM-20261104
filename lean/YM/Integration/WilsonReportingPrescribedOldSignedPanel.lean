import YM.Integration.WilsonReportingPrescribedOldGram
import YM.Integration.WilsonMatrixOriginalFiledPanel

/-! Exact signed prescribed-column comparison on the same separated physical
test and the same two marginal subtractions as the original Ward panel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldSignedPanel
open Function Set MeasureTheory Lattice Wilson RG Tree Precision Source Labels
open PhysicalNext.Repeat.Legato RGComparison.Core16 RG17 Extraction Table Spec MS MS.Menus MS.Local.Physical
open Extraction.Order Next.UVStress OPE OPE.Therm WilsonReportingPrescribedOldCoordinates
open private read_sub read_cont from YM.Integration.WilsonReportingPrescribedOldGram
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N per : ℕ}
local notation "Ω" => Config G (R.family.side N per)
local notation "site" => Site (R.family.side N per)
local notation "μtop" => scene R.family.path N per N

def entering (N per : ℕ) {h : ℕ} (hh : 4≤h) (v : R.family.label 4) : Panel R h :=
  Pi.single (⟨4,by omega⟩:Fin (h+1)) (WilsonCoherentTerminalFrame.coordinates R N per v)

theorem asReported {h:ℕ} (hh:4≤h) (v:R.family.label 4) (o:site) (U:Ω) :
    read R o U (entering R N per hh v)=R.family.O N per v o U := by
  let a : Fin (h+1) := ⟨4,by omega⟩
  have law := Descent.field_label_correct (C:=R.family) (N:=N) (p:=per) (o:=o)
      (WilsonCoherentTerminalFrame.coordinates R N per v)
  rw [WilsonCoherentTerminalFrame.named] at law
  unfold WilsonReportingPrescribedOldCoordinates.read entering
  rw [Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]
    exact (congrFun law U).symm
  · intro b _ ne
    rw [Pi.single_eq_of_ne ne,map_zero]
  · simp

def covariance (A B : Ω → ℝ) : ℝ := (∫U,A U*B U ∂μtop)-(∫U,A U ∂μtop)*(∫U,B U ∂μtop)

def separated (χ:ℂ→L[ℝ]ℝ) (φ:Test 2) (A B:site → Ω → ℂ) : ℝ :=
  R.family.S.a N^(4*2)*∑x : Fin 2 → site,(φ (cells R.family N per x)).re*
    covariance R (fun U=>(A (x 0) U).re) (fun U=>χ (B (x 1) U))

private theorem polarized (A B P Q : Ω → ℝ) (ha:Continuous A) (hb:Continuous B)
    (hp:Continuous P) (hq:Continuous Q) :
    covariance R A B-covariance R P Q=covariance R (A-P) B+covariance R P (B-Q) := by
  letI : IsProbabilityMeasure μtop := probability R.makes.wilson le_rfl
  have buy {f:Ω→ℝ} (hc:Continuous f) : Integrable f μtop :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold covariance
  have left : (fun U=>(A-P) U*B U)=(fun U=>A U*B U-P U*B U) := by ext U;exact sub_mul _ _ _
  have right : (fun U=>P U*(B-Q) U)=(fun U=>P U*B U-P U*Q U) := by ext U;exact mul_sub _ _ _
  have hAB : Integrable (fun U=>A U*B U) μtop := buy (ha.mul hb)
  have hPB : Integrable (fun U=>P U*B U) μtop := buy (hp.mul hb)
  have hPQ : Integrable (fun U=>P U*Q U) μtop := buy (hp.mul hq)
  rw [left,right,integral_sub hAB hPB,integral_sub hPB hPQ]
  simp only [Pi.sub_apply,integral_sub (buy ha) (buy hp),integral_sub (buy hb) (buy hq)]
  ring

variable {B:Deck G} (Q:MS.Land.Prescription B)
def issued (u:MS.Rake.Label B) (μ:ℝ) (k:ℕ) (o:site) (U:Ω) : ℂ :=
  ActualOriginalCalibratedColumns.weightedObservable R B Q u μ (R.family.side N per) o U k

private theorem issued_cont (u:MS.Rake.Label B) (μ:ℝ) (k:ℕ) (o:site) :
    Continuous (issued R Q u μ k o) := by
  have eq : issued R Q u μ k o=fun U=>read R o U (prescribed R Q u μ k) :=
    funext fun U=>WilsonReportingPrescribedOldCoordinates.independent R Q u o U μ k
  rw [eq]
  exact read_cont R o _

def residual (u:MS.Rake.Label B) (hu:4≤u.h) (μ:ℝ) (k:ℕ) (v:R.family.label 4)
    (o:site) (U:Ω) : ℂ :=
  read R o U (entering R N per hu v-prescribed R Q u μ k)

theorem field (u:MS.Rake.Label B) (hu:4≤u.h) (μ:ℝ) (k:ℕ) (v:R.family.label 4)
    (o:site) (U:Ω) :
    residual R Q u hu μ k v o U=R.family.O N per v o U-issued R Q u μ k o U := by
  unfold residual issued
  rw [read_sub,asReported,WilsonReportingPrescribedOldCoordinates.independent R Q u o U]

/-- No diagonal estimate or quotient by a scalar row is used. The entire
finite grid and each genuine covariance subtraction stay inside the price. -/
theorem original {f:Extraction.Order} {S:Table R.family.book} (F:Spec.Final R.family f S) (L:Layout F)
    (a b:ℝ→R.family.label 4) (χ:ℂ→L[ℝ]ℝ) (φ:Test 2) {r:ℝ} (hr:0<r)
    (u v:MS.Rake.Label B) (hu:4≤u.h) (hv:4≤v.h) (μ:ℝ) (k l:ℕ) (N per:ℕ) :
    let x := atRef L 4 r (N,per) (a r)
    let y := atRef L 4 r (N,per) (b r)
    let ψ := dilate hr φ
    WilsonMatrixOriginalFiledPanel.Value F L a b χ φ hr (N,per)-
        separated R (N:=N) (per:=per) χ ψ (issued R (N:=N) (per:=per) Q u μ k) (issued R (N:=N) (per:=per) Q v μ l)=
      separated R (N:=N) (per:=per) χ ψ (residual R (N:=N) (per:=per) Q u hu μ k x) (R.family.O N per y)+
        separated R (N:=N) (per:=per) χ ψ (issued R (N:=N) (per:=per) Q u μ k) (residual R (N:=N) (per:=per) Q v hv μ l y) := by
  dsimp only
  unfold WilsonMatrixOriginalFiledPanel.Value WilsonMatrixOriginalSignedReading.signed separated
  rw [←mul_sub,←mul_add]
  apply congrArg (fun z=>R.family.S.a N^(4*2)*z)
  rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←mul_sub,←mul_add]
  apply congrArg (fun z=>(dilate hr φ (cells R.family N per i)).re*z)
  let x:=atRef L 4 r (N,per) (a r)
  let y:=atRef L 4 r (N,per) (b r)
  have left : (fun U=>(residual R Q u hu μ k x (i 0) U).re)=
      (fun U=>(R.family.O N per x (i 0) U).re)-(fun U=>(issued R Q u μ k (i 0) U).re) := by
    funext U;rw [field];rfl
  have right : (fun U=>χ (residual R Q v hv μ l y (i 1) U))=
      (fun U=>χ (R.family.O N per y (i 1) U))-(fun U=>χ (issued R Q v μ l (i 1) U)) := by
    funext U;rw [field,map_sub];rfl
  rw [left,right]
  apply polarized
  · exact Complex.continuous_re.comp (R.family.continuousO ..)
  · exact χ.continuous.comp (R.family.continuousO ..)
  · exact Complex.continuous_re.comp (issued_cont R Q ..)
  · exact χ.continuous.comp (issued_cont R Q ..)

end YM.Integration.WilsonReportingPrescribedOldSignedPanel
