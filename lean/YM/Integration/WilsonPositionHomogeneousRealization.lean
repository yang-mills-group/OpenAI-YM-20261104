import YM.Integration.WilsonPositionHomogeneousCoefficients
import YM.Integration.WilsonPositionGradedCutoffs

/-! The numerical mass-independent correction in the prescribed position
frame. The finite grade inclusions commute exactly for every positive
coupling, and its perturbative expansion is the original Wilson adjustment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionHomogeneousRealization
open Function Filter Set Finset PowerSeries Maxwell XSpace XSpace.Normalize MS MS.Land FVA2 FVA2.Register FVA2.Scale
open WilsonPositionHomogeneousCoefficients
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} (Z : WilsonPrescription G)

def correction (d : ℕ) (t : ℝ) : Change G d :=
  (guide G d).symm (WilsonPositionGradedCutoffs.field (dossier Z) d t)

theorem sheet {t : ℝ} {N : ℕ} (cut:∀n : ℕ,N≤n→WilsonPositionGradedCutoffs.weight (dossier Z) n t=0) (d : ℕ) :
    correction Z d t=∑n∈range N,WilsonPositionGradedCutoffs.weight (dossier Z) n t • letter Z d n := by
  apply (guide G d).injective
  simp only [correction,LinearEquiv.apply_symm_apply,map_sum,map_smul]
  exact WilsonPositionGradedCutoffs.exactly (dossier Z) cut d

private def scan (d : ℕ) : Change G d→ₗ[ℝ] FieldEnd G d :=
  ((Level.diag (G:=G) (d:=d)).restrictScalars ℝ).comp (Change G d).subtype

private def atField {d : ℕ} (v : Sec G d) : Change G d→ₗ[ℝ] Sec G d where
  toFun u:=u.val v
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

theorem diagonal (H : Warrant Z) (d : ℕ) {t : ℝ} (ht:0<t) :
    Level.diag (stand (correction Z d t))=1 := by
  obtain ⟨N,hn⟩:=WilsonPositionGradedCutoffs.finite (dossier Z) ht
  have phi:scan (G:=G) d (correction Z d t)=0 := by
    rw [sheet Z hn d,map_sum]
    apply sum_eq_zero
    intro n _
    rw [map_smul]
    change _ • Level.diag (letter Z d n).val=0
    rw [absent Z H d n,smul_zero]
  change Level.diag (1+(correction Z d t).val)=1
  rw [map_add,Level.diagonal_one,show Level.diag (correction Z d t).val=0 from phi,add_zero]

theorem includes (H:Warrant Z) {d e : ℕ} (h:d≤e) {t:ℝ} (ht:0<t) (v: Sec G d) :
    stand (correction Z e t) (up h v) = up h (stand (correction Z d t) v) := by
  obtain ⟨N,hn⟩:=WilsonPositionGradedCutoffs.finite (dossier Z) ht
  simp only [stood,map_add]
  apply congrArg (fun x=>up h v+x)
  let lo:=((up (G:=G) h).restrictScalars ℝ).comp (atField v)
  let hi:=atField (up h v)
  change hi (correction Z e t)=lo (correction Z d t)
  rw [sheet Z hn e,sheet Z hn d,map_sum,map_sum]
  apply sum_congr rfl
  intro n _
  rw [map_smul,map_smul]
  exact congrArg (fun x:Sec G e=>WilsonPositionGradedCutoffs.weight (dossier Z) n t • x) (chart Z H h n v)

/-- All real coefficients of the true field adjustment in a physical
asymptotic representative chosen once, before the order. -/
theorem expansion (d q:ℕ) :
    ∃ A : ℝ,0≤A ∧ ∀ᶠ t : ℝ in 𝓝[>] 0,
      ‖guide G d (correction Z d t)-∑n∈range (q+1),t^n • guide G d (letter Z d n)‖≤A*t^(q+1) := by
  simpa only [correction,LinearEquiv.apply_symm_apply,dossier] using
    WilsonPositionGradedCutoffs.expansion (dossier Z) d q

theorem smooth (d : ℕ) : ContDiffOn ℝ ∞ (fun t=>guide G d (correction Z d t)) (Ioi 0) := by
  simpa only [correction,LinearEquiv.apply_symm_apply] using WilsonPositionGradedCutoffs.smooth (dossier Z) d

end YM.Integration.WilsonPositionHomogeneousRealization

