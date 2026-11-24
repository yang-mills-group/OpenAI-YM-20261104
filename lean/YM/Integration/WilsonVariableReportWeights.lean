import YM.Integration.WilsonPhysicalReportWeights
import YM.Next.UV_STRESS.Vary

/-! The physical input vectors may move with the diagnostic mesh. Their
complete grade and coordinate sum is paid uniformly in their true norms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVariableReportWeights
open Function Filter Real MeasureTheory Lattice Wilson RG Cells OPE OPE.Orbits OPE.Cards
open Source Labels Trace.Pilot Trace.Physical Trace.Physical.GermGraph Work.G08 RG16.Literal
open StressFlux.Matching Frontier6.Road EngineeringWeightedReadout WilsonWholeLimit
open MultilinearCellCapture FilteredIntrinsicGramReadout FilteredWilsonProduct SharedIntrinsicWilsonGrid
open WilsonPhysicalReportWeights Next.UVStress Finset
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ}

private def word (F : Spec.Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (t : ℝ) (g : Grades d) (a : Indices C (levels g)) :
    MultilinearMap ℂ (fun i => (Climb.Bel C.book).Field (d i)) ℂ :=
  (MultilinearMap.mkPiAlgebra ℂ I ℂ).compLinearMap fun i =>
    (LinearMap.proj (a i)).comp ((S.representative _).comp ((Q.cutTest _ _).comp (J t (d i)).toLinearMap))

theorem paid (F : Spec.Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J) :
    ∀ᶠ t in trail, ∀ v : (i : I) → (Climb.Bel C.book).Field (d i),
      (∑ g : Grades d, gradePrice F Q J v g t) ≤ exp (2*LogV t)*(∏ i,‖v i‖) := by
  classical
  let E := fun i => (Climb.Bel C.book).Field (d i)
  let cap (u : Code E) := ∏ i, ‖((Module.finBasis ℂ (E i)).coord (u i)).toContinuousLinearMap‖
  let K := ∑ u : Code E, cap u
  have budget := (Real.tendsto_exp_atTop.comp PhysMS.to_log_zoom).eventually_ge_atTop K
  filter_upwards [Filter.eventually_all.2 (fun u : Code E => price F Q J H (combination E u)),budget] with t rows fixedFee
  intro v
  let V := ∏ i,‖v i‖
  have vn : 0 ≤ V := prod_nonneg fun _ _ => norm_nonneg _
  have invoice (u : Code E) : ‖coords E u v‖ ≤ cap u*V := by
    unfold coords cap V
    rw [norm_prod,←prod_mul_distrib]
    exact prod_le_prod (fun _ _=>norm_nonneg _) fun i _ => ((Module.finBasis ℂ (E i)).coord (u i)).toContinuousLinearMap.le_opNorm _
  let read := fun (g : Grades d) (a : Indices C (levels g)) (v' : (i : I) → E i) => weight (component F Q J v' g t) a
  have basisBound (g : Grades d) (a : Indices C (levels g)) :
      ‖read g a v‖ ≤ ∑ u : Code E, ‖coords E u v‖*‖read g a (combination E u)‖ := by
    change ‖word F Q J t g a v‖ ≤ _
    rw [basis_tuple E v (word F Q J t g a)]
    exact (norm_sum_le ..).trans_eq (Finset.sum_congr rfl fun u _ => norm_mul _ _)
  calc
    _ ≤ ∑ g : Grades d, ∑ a : Indices C (levels g), ∑ u : Code E, ‖coords E u v‖*‖read g a (combination E u)‖ :=
      sum_le_sum fun g _ => sum_le_sum fun a _ => basisBound g a
    _ = ∑ g : Grades d, ∑ u : Code E, ∑ a : Indices C (levels g), ‖coords E u v‖*‖read g a (combination E u)‖ :=
      sum_congr rfl fun _ _ => sum_comm
    _ = ∑ u : Code E, ‖coords E u v‖*(∑ g : Grades d, gradePrice F Q J (combination E u) g t) := by
      rw [sum_comm]
      simp only [gradePrice,mul_sum,read]
    _ ≤ ∑ u : Code E, cap u*(exp (LogV t)*V) := sum_le_sum fun u _ => calc
      _ ≤ ‖coords E u v‖*exp (LogV t) := mul_le_mul_of_nonneg_left (rows u) (norm_nonneg _)
      _ ≤ cap u*V*exp (LogV t) := mul_le_mul_of_nonneg_right (invoice u) (exp_pos _).le
      _ = _ := by ring
    _ = K*(exp (LogV t)*V) := (sum_mul ..).symm
    _ ≤ exp (LogV t)*(exp (LogV t)*V) := mul_le_mul_of_nonneg_right fixedFee (mul_nonneg (exp_pos _).le vn)
    _ = _ := by rw [←mul_assoc,←exp_add]; exact congrArg (fun c : ℝ => exp c*V) (by ring)

end YM.Integration.WilsonVariableReportWeights
