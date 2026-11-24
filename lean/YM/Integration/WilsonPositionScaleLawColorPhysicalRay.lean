import YM.Integration.WilsonPositionScaleLawColorCocycle

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawColorPhysicalRay
open Function Filter Set Spec Table Extraction OPE Climb Trace.Pilot PhysMS Maxwell Maxwell.Free
open XSpace XSpace.Stab XSpace.Normalize MS MS.Land FVA2 FVA2.Dframe FVA2.Position.OpenAxis
open WilsonPhysicalPositionDiscreteBranches (field)
open WilsonPhysicalPositionBornCandidates (possible)
open WilsonPhysicalPositionBornTransition (present)
open WilsonPositionScaleLawColorReading (reader Bill)
open WilsonPositionThermometerGradedSource (source)
open WilsonPhysicalPositionUniformBranches (change)
open WilsonPositionScaleLawCompactNative (positive)
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawCompactBranch
open WilsonPositionScaleLawColorAtHome (Quote)
open WilsonPositionPrescribedFormalTest (raw)
open scoped Topology Classical
open WilsonPositionScaleLawColorActor (Cone Faculty)
open WilsonPositionScaleLawColorLive (Original)
variable {G : Gauge}

theorem closedRay {I E : Type*} {l : Filter I} [NeBot l] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : E) {Y : I → E} {y : E} (approach : Tendsto Y l (𝓝 y))
    (positive : ∀ᶠ i in l, ∃ s : ℝ, (0 ≤ s) ∧ Y i = (s:ℂ) • x) :
    ∃ s : ℝ, (0 ≤ s) ∧ y = (s:ℂ) • x := by
  by_cases hx : x = 0
  · have zero : ∀ᶠ i in l, Y i = 0 := positive.mono (fun i hi => by
      obtain ⟨s,_,hs⟩ := hi
      simpa [hx] using hs)
    exact ⟨0,le_rfl,by simpa using tendsto_nhds_unique approach (tendsto_const_nhds.congr' (zero.mono (fun _ h => h.symm)))⟩
  · have nz : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have rates := approach.norm.div_const ‖x‖
    have measured : ∀ᶠ i in l, (↑(‖Y i‖ / ‖x‖):ℂ) • x = Y i := positive.mono (fun i hi => by
      obtain ⟨s,paid,hs⟩ := hi
      rw [hs,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg paid,mul_div_cancel_right₀ _ nz])
    refine ⟨‖y‖ / ‖x‖,div_nonneg (norm_nonneg _) (norm_nonneg _),?_⟩
    exact tendsto_nhds_unique approach
      (((Complex.continuous_ofReal.continuousAt.tendsto.comp rates).smul (tendsto_const_nhds (x:=x))).congr' measured)

open Next.Rank OJoint WilsonMeasuredPublicEntranceMarkedQuadratics WilsonMeasuredPublicEntranceQuadraticFiled
variable [RangeSpec] {C : Family G} {f : Extraction.Order} {S : Table C.book} (F : Final C f S) (J : ℝ → tower S) (lead : Leading F J)
def Ray (J : ℝ → tower S) : Prop :=
  ∀ᶠ z in (sweep : Filter (ℝ × Ratio)), ∃ s : ℝ, (0 ≤ s) ∧ change J 4 z.1 z.2.val (positive z.2) (stepField C) = (s:ℂ) • stepField C
include lead in
theorem original {d : ℕ} (h : 6≤d) (a : MoveSpace G d) (earned : Ray J)
    {I : Type*} {l : Filter I} [NeBot l] (dates : I → ℝ × Ratio) (home : Tendsto dates l sweep) :
    let up : 4≤d := by omega
    let w := (scheme C.labels).rise up (stepField C)
    Tendsto (fun i => change J d (dates i).1 (dates i).2.val (positive (dates i).2) w) l
      (𝓝 (present (C:=C) (field a) w)) → Cone C h a := by
  intro up w understood
  have both := (home.eventually (WilsonPositionScaleLawGuardNest.natural F J lead up)).and (home.eventually earned)
  obtain ⟨t,nonnegative,read⟩ := closedRay w understood (both.mono (fun i hit => by
    obtain ⟨s,sign,eq⟩ := hit.2
    refine ⟨s,sign,?_⟩
    rw [show w=(scheme C.labels).rise up (stepField C) from rfl,hit.1,eq,map_smul]))
  exact ⟨t,nonnegative,0,by simpa using read⟩
end YM.Integration.WilsonPositionScaleLawColorPhysicalRay
end
