import YM.Integration.WilsonPositionOriginalDiagnosticRead
import YM.Integration.WilsonPositionPrescribedRootPrice

/-! Actual compact field-normalization tests of the original run, coupled to
the root of the independently prescribed position scheme. The invoice is a
finite sum of named signed comparisons of physical film words. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticPurse
open Function Filter Set Finset Metric MeasureTheory Extraction Table Spec OPE Climb PhysMS Maxwell
open Trace.Pilot XSpace XSpace.Normalize XSpace.Normalize.Fray FVA2 FVA2.Arrival MS MS.Land
open MS.Local.Physical MS.Menus MS.Theater WilsonPositionOriginalDiagnosticRead
open WilsonPositionPrescribedFormalTest WilsonPositionPrescribedTariff
open scoped Topology BigOperators Classical
variable {G:Gauge} (B:Deck G) (V:Store G) {d:ℕ}

def fixed (i:Fin (V.survey d).n) (k:Fin ((V.survey d).scope i).n→Pin G d) : Window G d :=
  ⟨_,((V.survey d).scope i).t,fun j=>Module.finBasis ℝ (Sec G d) (k j)⟩

def invoice (P Q:Prediction G d) : ℝ :=
  ∑ i:Fin (V.survey d).n, ∑ k:Fin ((V.survey d).scope i).n→Pin G d,
    bill B (fixed V i k) P Q

theorem fee (P Q:Prediction G d) :
    ‖(V.survey d).purse P-(V.survey d).purse Q‖ ≤ invoice B V P Q := by
  have nn (w:Window G d) : 0≤bill B w P Q :=
    sum_nonneg fun _ _=>mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have nz (i:Fin (V.survey d).n) : 0≤∑ k:Fin ((V.survey d).scope i).n→Pin G d, bill B (fixed V i k) P Q :=
    sum_nonneg fun _ _=>nn _
  apply (pi_norm_le_iff_of_nonneg (sum_nonneg fun _ _=>nz _)).mpr
  intro i
  apply le_trans _ (single_le_sum (f:=fun j=>∑ k:Fin ((V.survey d).scope j).n→Pin G d, bill B (fixed V j k) P Q)
    (fun _ _=>nz _) (mem_univ i))
  apply (pi_norm_le_iff_of_nonneg (nz i)).mpr
  intro k
  apply le_trans _ (single_le_sum (f:=fun j=>bill B (fixed V i j) P Q) (fun _ _=>nn _) (mem_univ k))
  change ‖watch (fixed V i k) P - watch (fixed V i k) Q‖ ≤ _
  rw [signed B _ P,signed B _ Q,←sum_sub_distrib]
  apply (norm_sum_le ..).trans
  exact sum_le_sum fun a _=>by rw [←mul_sub,norm_mul]

variable (ν:ℝ) (T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (q:ℕ)
variable {C:Family G} {f:Extraction.Order} {S:Table C.book} (F:Final C f S) (J:ℝ→PhysMS.tower S)

/-- Through every fixed perturbative order on the elected physical hierarchy,
only the original signed compact rows at this single finite panel are charged. -/
theorem original (lead:PhysMS.Leading F J) {t:ℝ→ℝ} (small:Tendsto t Trace.Pilot.trail (𝓝 0)) :
    ∃ L A:ℝ, 0≤L ∧ 0≤A ∧ ∀ᶠ r in Trace.Pilot.trail,
      ‖guide G d (WilsonPositionPrescribedScreen.correction F J V d r) -
        WilsonPositionPrescribedRootPrice.native V ν T d q (t r)‖ ≤
      L*invoice B V (WilsonPositionPrescribedScreen.hierarchy F J d r) (raw ν T d q (t r))+
        A*|t r|^(q+1) := by
  obtain ⟨L,A,hL,hA,h⟩:=WilsonPositionPrescribedRootPrice.physical V ν T d q F J lead small
  refine ⟨L,A,hL,hA,?_⟩
  filter_upwards [h] with r at_r
  rw [←menu V ν T d q (t r)] at at_r
  exact at_r.trans (add_le_add (mul_le_mul_of_nonneg_left (fee B V _ _) hL) le_rfl)

end YM.Integration.WilsonPositionOriginalDiagnosticPurse
