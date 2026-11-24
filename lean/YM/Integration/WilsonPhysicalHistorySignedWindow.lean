import YM.Integration.WilsonPhysicalHistoryPositiveTower
import YM.Integration.WilsonPhysicalHistoryBirthClock
import YM.Integration.WilsonPosteriorProjectionMaterial
import YM.Integration.FVA1Physical.Wilson.ChartEnvelope

/-! The signed telescoping error of prescribed dated fields is measured on
the original Wilson marginals throughout the actual growing cutoff window. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistorySignedWindow
open Function Filter Finset Set MeasureTheory Lattice RG YM.Wilson OPE OPE.Therm Push.GridApprox
open WilsonCoeffUV PhysicalNext.Repeat.Legato WilsonReportForwardTransfer
open Precision Tree Exterior Push.Uniform MSbar MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Cacao MSbar.Mosaic MSbar.Rolling MSbar.Bulk MSbar.Lis MSbar.Bakery.Film MSbar.Midpoint MSbar.Measuring
open FVA1Physical.Wilson FVA1Physical.Round2.Curvature RG01.Kernel
open RG16 RG16.Literal Pert.Asymptotics WilsonPhysicalExteriorMeshStops
open scoped BigOperators Classical
variable {G : Gauge}

def debt (R : Run G) {N per j : ℕ} (X Y : Config G (R.family.side j per)→ℂ) : ℝ :=
  ∫ V, ‖X V-Y V‖ ∂scene R.family.path N per j

private theorem triangle (R : Run G) {N per j : ℕ} (X Y Z : Config G (R.family.side j per)→ℂ)
    (hX : Integrable X (scene R.family.path N per j))
    (hY : Integrable Y (scene R.family.path N per j))
    (hZ : Integrable Z (scene R.family.path N per j)) :
    debt R (N:=N) X Z ≤ debt R (N:=N) X Y+debt R (N:=N) Y Z := by
  calc
    _ ≤ ∫ V, ‖X V-Y V‖+‖Y V-Z V‖ ∂scene R.family.path N per j :=
      integral_mono (hX.sub hZ).norm ((hX.sub hY).norm.add (hY.sub hZ).norm) (fun V=>by
        change ‖X V-Z V‖ ≤ ‖X V-Y V‖+‖Y V-Z V‖
        simpa only [dist_eq_norm] using dist_triangle (X V) (Y V) (Z V))
    _ = _ := integral_add (hX.sub hY).norm (hY.sub hZ).norm

private theorem self (R : Run G) {N per j : ℕ} (top : j ≤ N)
    (X : Config G (R.family.side j per)→ℂ) :
    exterior (C:=R.family) (N:=N) (le_refl j) X = X := by
  funext V
  unfold WilsonReportForwardTransfer.exterior
  rw [pushTo_self]
  unfold weighted
  have pos := dose_positive R.makes.wilson top V
  have nz : (↑(dose (H:=R.family.path) (p:=per) j V N) : ℂ) ≠ 0 := by exact_mod_cast pos.ne'
  field_simp

/-- No length loss: signed full-source discrepancies at their own dates are
charged exactly once, even when the cutoff distance grows with the endpoint.
No equality of the independently specified predecessor and the return is assumed. -/
theorem accumulate (R : Run G) {N per k t : ℕ} (kt : k ≤ t) (top : t ≤ N)
    (X : Config G (R.family.side t per)→ℂ) (hX : Integrable X (scene R.family.path N per t))
    (B : (j:ℕ) → Config G (R.family.side j per) → ℂ)
    (hB : ∀ j, j ≤ N → Integrable (B j) (scene R.family.path N per j)) :
    debt R (N:=N) (exterior (C:=R.family) (N:=N) kt X) (B k) ≤ debt R (N:=N) X (B t) +
      ∑ j∈Finset.Ico k t,debt R (N:=N) (exterior (C:=R.family) (N:=N) j.le_succ (B (j+1))) (B j) := by
  induction t,kt using Nat.le_induction with
  | base => simp only [self R top X,Finset.Ico_self,Finset.sum_empty,add_zero,le_refl]
  | succ t ht ih =>
      let Y := exterior (C:=R.family) (N:=N) t.le_succ X
      let Q := exterior (C:=R.family) (N:=N) t.le_succ (B (t+1))
      have yt : Integrable Y (scene R.family.path N per t) := (contract (C:=R.family) R.makes t.le_succ top X hX).1
      have qt : Integrable Q (scene R.family.path N per t) := (contract (C:=R.family) R.makes t.le_succ top _ (hB _ top)).1
      have tN := t.le_succ.trans top
      have earlier := ih tN Y yt
      have d1 : debt R (N:=N) Y Q ≤ debt R (N:=N) X (B (t+1)) :=
        WilsonPhysicalHistoryPositiveTower.next_distance R top X (B (t+1)) hX (hB _ top)
      have stage : debt R (N:=N) Y (B t) ≤ debt R (N:=N) X (B (t+1))+debt R (N:=N) Q (B t) :=
        (triangle R Y Q (B t) yt qt (hB _ tN)).trans (add_le_add d1 le_rfl)
      rw [Finset.sum_Ico_succ_top ht]
      rw [← WilsonPhysicalHistoryPositiveTower.cascade R ht t.le_succ top X]
      change debt R (N:=N) (exterior (C:=R.family) (N:=N) ht Y) (B k) ≤ _
      exact earlier.trans ((add_le_add stage le_rfl).trans_eq (by ring))

/-- The finite formal fields are read at their own genuine regulator, using
the actual bounded group logarithm on the full finite configuration. -/
def filed (R : Run G) (N per j p : ℕ) (T : Bool→Nesting G (R.family.side j per))
    (U : Config G (R.family.side j per)) : ℂ :=
  let g := regulatorRun R.family N per j
  (clockReading p g (T false) (chartLog g U) : ℝ) + Complex.I * (clockReading p g (T true) (chartLog g U) : ℝ)

/-- Integrability costs no agreement assumption on any dated polynomial;
it follows from the original finite chart envelope on the same measured board. -/
theorem filed_integrable (R : Run G) {N per j : ℕ} (top : j ≤ N)
    (p : ℕ) (T : Bool→Nesting G (R.family.side j per)) :
    Integrable (filed R N per j p T) (scene R.family.path N per j) := by
  letI : IsProbabilityMeasure (scene R.family.path N per j) := probability R.makes.wilson top
  let g := regulatorRun R.family N per j
  have h (part : Bool) : Integrable (fun U : Config G (R.family.side j per)=>
      (↑(clockReading p g (T part) (chartLog g U)):ℂ)) (scene R.family.path N per j) :=
    ((chartLog_envelope g (clockReading_continuous p g (T part))).integrable _).ofReal
  exact (h false).add ((h true).const_mul Complex.I)

/-- Same-run comparison of any complete original signed terminal experiment
with the whole prescribed dated polynomial family on the physical subwindow. -/
theorem dated (R : Run G) (p : ℕ) {N per k t : ℕ} (kt : k ≤ t) (top : t ≤ N)
    (X : Config G (R.family.side t per)→ℂ) (hX : Integrable X (scene R.family.path N per t))
    (T : (j:ℕ) → Bool → Nesting G (R.family.side j per)) :
    let B := fun j=>filed R N per j p (T j)
    debt R (N:=N) (exterior (C:=R.family) (N:=N) kt X) (B k) ≤ debt R (N:=N) X (B t) +
      ∑ j∈Finset.Ico k t,debt R (N:=N) (exterior (C:=R.family) (N:=N) j.le_succ (B (j+1))) (B j) :=
  accumulate R kt top X hX _ (fun j h=>filed_integrable R h p (T j))

end YM.Integration.WilsonPhysicalHistorySignedWindow

