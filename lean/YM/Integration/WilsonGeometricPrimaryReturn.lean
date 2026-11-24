import YM.Integration.WilsonCapturedPrimaryTruePanel
import YM.Integration.WilsonGeometricSignedClear

/-! Read the whole true finite primary from a signed difference priced on the original healthy fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGeometricPrimaryReturn
open Finset Filter Lattice RG Wilson Source Labels Extra.Histories Push.Local
open Next.Foundations Planned.AtomRegular ProjectorNext.Equivariance Trace.Physical.Germ
open PhysicalNext.Repeat.Legato Pert.Asymptotics Stationary Comparison.RG02
open WilsonCapturedPrimaryPaid WilsonCapturedPrimaryReading
open scoped Classical BigOperators Topology

variable {G : Gauge} {d : ℕ} (F : Frame G d) (A : Hol G) (S : SectionData F)

theorem original (R : Run G) (simple : G.Simple) (T : ℕ) {N per i : ℕ} (live : i<N)
    (wrapped : (eventually_atTop.mp (Trace.Physical.GermGraph.cut_flat R.family simple 0)).choose ≤ i)
    (late : (eventually_atTop.mp (WilsonCapturedPrimaryOnRun.readouts R simple F A S T 0 1 le_rfl)).choose ≤ i)
    (P : RG.Rep G (R.family.side i per)) (point : P.p=R.family.path.levels.budget i)
    (support : 1≤P.p.supportExponent) (rank : d+1≤P.p.order)
    (o : Site (R.family.side i per)) (h : Coefficient F (R.family.side i per)) {w κ rough α : ℝ}
    (read : Readable A S P.p (R.family.side i per) w) (form : h.Format o A P) (rem : h.remBound o P κ rough)
    (ap : 0≤α) :
    let g := regulatorRun R.family N per (i+1)
    let I := WilsonCapturedPrimaryDecoder.invoice F A d
    let wrap := WilsonCapturedPrimaryCoreBill.wrapFee F A
    (I*g^T)*w≤1/2 →
    (∀ U : Config G (R.family.side i per), flags P.p.threshold U=∅ → ‖reading S P o h U‖≤α*g^(grade T d 1)) →
    F.coeffSize (projection F A P.p.threshold o h) ≤ 2*(I*g^T)*(α+w*(wrap*rough)+rough) ∧
    F.coeffSize h.x ≤ 2*(I*g^T)*(α+w*(wrap*rough)+rough)+wrap*rough := by
  intro g I wrap small heard
  have fzero : WilsonCapturedPrimaryDecoder.forecast F (fun _ => 0) = 0 := by
    unfold WilsonCapturedPrimaryDecoder.forecast
    simp only [Polynomial.coeff_zero,mul_zero]
    exact map_zero _
  have panel := WilsonCapturedPrimaryTruePanel.original F A S R simple T d le_rfl live wrapped late P
    point support rank o h read form rem ap (fun _ => 0) (by simp) small
    (fun p _ j _ _ _ clear => by simpa using heard _ clear)
  have coefzero : F.coeffSize (0:F.Coeff) = 0 := by simp [Frame.coeffSize]
  rw [fzero,sub_zero,map_zero,coefzero,zero_add] at panel
  have short : wraps P.p (R.family.side i per)≤1 := by
    rw [point]
    have cap := (eventually_atTop.mp (Trace.Physical.GermGraph.cut_flat R.family simple 0)).choose_spec i wrapped per
    simpa using cap
  have fit := (germ_close F A).choose_spec.2 P h form rem read.order read.power
  have rate := (germ_close F A).choose_spec.1.le
  have paid : 0 ≤ rough := by obtain ⟨a,b,sa,sb,v,_⟩ := rem; linarith only [sa,sb,v]
  let p := projection F A P.p.threshold o h
  have difference : F.coeffSize (h.x-p) ≤ wrap*rough := calc
    _ ≤ (F.extra+1:ℕ)*‖h.x-p‖ := size_le_norm F _
    _ = (F.extra+1:ℕ)*‖p-h.x‖ := by rw [norm_sub_rev]
    _ ≤ (F.extra+1:ℕ)*((germ_close F A).choose*wraps P.p (R.family.side i per)*rough) :=
      mul_le_mul_of_nonneg_left fit (Nat.cast_nonneg _)
    _ ≤ (F.extra+1:ℕ)*((germ_close F A).choose*rough) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right rate short) paid) (Nat.cast_nonneg _)
    _ = _ := by dsimp only [wrap,WilsonCapturedPrimaryCoreBill.wrapFee]; ring
  refine ⟨panel,?_⟩
  calc
    _ ≤ F.coeffSize p + F.coeffSize (h.x-p) := by
      unfold Frame.coeffSize
      rw [←sum_add_distrib]
      exact sum_le_sum fun j _ => calc
        ‖h.x j‖ = ‖p j+(h.x j-p j)‖ := congrArg norm (by ring)
        _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add panel difference

end YM.Integration.WilsonGeometricPrimaryReturn
