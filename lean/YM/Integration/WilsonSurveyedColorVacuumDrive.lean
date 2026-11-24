import YM.Integration.WilsonSurveyedColorAppointed
import YM.Integration.WilsonSurveyedColorRegulator
import YM.Integration.WilsonSurveyedColorSubtraction

/-! Actual quadratic and linear forcing in the nominated dimensional MS
recursion, including the implicit dimensionally integrated cycle. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorVacuumDrive
open Function Set Filter Finset MS Plane Koszul Heat Flux Arts Pilot Spin Arc Wire Rock Path
open Landau City Oceans Garment Garment.Wave Garment.Wick Shine Hem Mell Pearl Train Dock Emit
open WilsonSurveyedColorQuotient WilsonSurveyedColorPilot WilsonSurveyedColorFlow
open WilsonSurveyedColorRegulator WilsonSurveyedColorSubtraction
open scoped Classical BigOperators Topology
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)

theorem atSlot (F : Flats G) (k : ℕ) : ledger U F k = coat U (F k) := by
  simpa only [Nat.add_zero] using blade 0 F (coat U) k

theorem initial (same : WilsonSurveyedColorCurvature.Preserves U) (k : ℕ) :
    coat U (gloss (Motif.pulseX G) k) = gloss (Motif.pulseX G) k := by
  funext z m
  exact WilsonSurveyedColorCurvature.opening U same k m

theorem arbor (s : ℝ) (F H : Mob G) :
    allDims U (Arts.arbor (A0 G s) F H) =
      Arts.arbor (A0 G s) (allDims U F) (allDims U H) := by
  funext m
  exact connected U _ _ _ ((cl_a G s) m)

private theorem both (i j : ℕ) (f g : Coat G) :
    drive0 G (Finsupp.single i f) (Finsupp.single j g) =
      Finsupp.single (j+i) (tapeB (squad (A0 G 0)) f g) := by
  unfold drive0 TreeN
  rw [explosionP,Finsupp.sum_single_index,blast_sl]
  ext F
  simp [blap]

theorem drive (F H : Flats G) :
    ledger U (drive0 G F H) = drive0 G (ledger U F) (ledger U H) := by
  induction F using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,LinearMap.add_apply,hx,hy]
  | single i f =>
    induction H using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add,hx,hy]
    | single j g =>
      simp only [both,ledger,blast_sl,Nat.add_zero]
      congr 1
      funext z
      exact arbor U 0 _ _

theorem bulk (F : ℕ → Flats G) (k : ℕ) :
    ledger U (program G k F) = program G k (fun i => ledger U (F i)) := by
  simp only [program,map_smul,map_sum,drive]

theorem marked (F H : ℕ → Flats G) (k : ℕ) :
    ledger U (platform F k H) =
      platform (fun i => ledger U (F i)) k (fun i => ledger U (H i)) := by
  simp only [platform,map_sum,drive]

theorem cycle {b : Bool} {t u r v : ℤ} {F H : Flats G}
    (left : ClockD b t r F) (right : ClockD b u v H)
    (prior : Pact (ledger U F) H) : Pact (ledger U (step0 G F)) (step0 G H) := by
  intro k
  cases k with
  | zero =>
    rw [atSlot]
    change Spotty (coat U (blast 1 _ F 0)) (blast 1 _ H 0)
    rw [bland (show 0<1 by decide),bland (show 0<1 by decide),map_zero]
  | succ k =>
    rw [atSlot]
    change Spotty (coat U (blast 1 _ F (k+1))) (blast 1 _ H (k+1))
    rw [blade,blade]
    filter_upwards [prior k,sunny (left k).fine.tune,sunny (right k).fine.tune,high0] with z hz hF hH ht
    rw [atSlot] at hz
    change allDims U (feeD z • port z (A0 G 0) (F k z)) = feeD z • port z (A0 G 0) (H k z)
    rw [map_smul,dollar (c_bo 0) hF ht,dollar (c_bo 0) hH ht]
    congr 1
    funext m
    exact oceanColor U (fun _ => line U _) hF hH (c_bo 0) ht (fun n => congrFun hz n)

end YM.Integration.WilsonSurveyedColorVacuumDrive
end
