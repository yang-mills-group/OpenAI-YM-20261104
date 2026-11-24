import YM.Integration.WilsonMovingForkTubeJets
import YM.Integration.WilsonNormalizedReflectedForm
import YM.Integration.WilsonMacroscopicRichTwoDatePivot
import YM.Integration.WilsonViewerElectedHierarchy

/-! The compact mean on the actual matching frame has a holomorphic slice
at every separated shape and in every unit direction on its elected run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalHomogeneousTube
open Filter Function Set Metric Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace Trace.Pilot PhysMS Climb GapsContact
open OPE.Orbits (Reader)
open OPE OPE.Orbits.Reader Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMacroscopicRichTwoDatePivot WilsonViewerElectedHierarchy
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J : ℝ → PhysMS.tower S} {L : EveryPhase.Almanac F} {Y : (Bel R.family.book).Hierarchy}
    {arch : Trace.Terrace.Arch R.family} {ℓ : Ultrafilter (ℕ×ℕ)}
    {simple : G.Simple} {cohort : Ultrafilter (ℕ×ℕ) → Prop}
    (run : Selected.{u} F L Q J Y arch ℓ simple cohort) (Z : WilsonPrescription G)

include run in
theorem own (d : ℕ) (v : RG17.Free R.family d) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ r in trail,
    Ascent.cost F d r (homogeneous F J Z r d v) ≤ B := by
  obtain ⟨B,hB,cap⟩ := WilsonNormalizedReflectedForm.uniform F J Z.store run.leading d
    (show 0 ≤ ‖v‖+1 by positivity)
  have near := (WilsonMacroscopicRichTwoDatePivot.field F J Z run.leading run.obeys simple d v).norm
  have bounded := near.eventually (ge_mem_nhds (show ‖v‖ < ‖v‖+1 by linarith))
  refine ⟨B,hB,?_⟩
  filter_upwards [cap,bounded] with r paid close
  have price := paid false (active F J Z r d v) close
  change Ascent.cost F d r (J r d ((J r d).symm (homogeneous F J Z r d v))) ≤ B at price
  simpa using price

include run in
theorem original {n : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → RG17.Free R.family (d i))
    {η : ℝ} (gap : 0 < η) :
    ∃ (ρ A : ℝ) (p : ℕ), 0 < ρ ∧ 0 ≤ A ∧ ∀ᶠ r in trail, ∀ x : Points n,
      (∀ i j : Fin n, i ≠ j → η ≤ dist (x i) (x j)) → ∀ a : Points n, ‖a‖ ≤ 1 →
      ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 ρ) ∧
        (∀ z ∈ closedBall 0 ρ, ‖g z‖ ≤ A*|LogV r|^p) ∧
        ((fun t : ℝ => S.classMoment S d (r • (x+t • a))
          (fun i => homogeneous F J Z r (d i) (v i))) =ᶠ[𝓝 0] fun t : ℝ => g t) := by
  choose B hB ownPrice using fun i => own run Z (d i) (v i)
  obtain ⟨ρ,hρ,δ,hδ,A,hA,p,tube⟩ := WilsonMovingForkTubeJets.model F simple run.bliss d gap
  have hd : 0 < δ := hδ.1
  have fixed : 0 ≤ ∏ i,B i := Finset.prod_nonneg fun i _ => hB i
  refine ⟨ρ,A*δ⁻¹^p*(∏ i,B i),p,hρ,by positivity,?_⟩
  filter_upwards [tube,eventually_all.mpr ownPrice] with r rooms wages x sep a ha
  obtain ⟨g,disk,size,reads⟩ := rooms x sep a ha (fun i => homogeneous F J Z r (d i) (v i))
  refine ⟨g,disk,?_,reads⟩
  intro z hz
  have owners := Finset.prod_le_prod
    (fun i (_ : i ∈ Finset.univ) => (Ascent.cost_pos F (d i) r _))
    (fun i (_ : i ∈ Finset.univ) => wages i)
  apply (size z hz).trans
  have book : (LogV r/δ)^p ≤ |LogV r|^p*δ⁻¹^p := by
    rw [div_eq_mul_inv,mul_pow,← abs_pow]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (inv_pos.mpr hδ.1).le _)
  calc
    _ ≤ (A*(|LogV r|^p*δ⁻¹^p))*(∏ i,B i) := by
      apply mul_le_mul _ owners (Finset.prod_nonneg fun i _ => (Ascent.cost_pos F (d i) r _)) (by positivity)
      exact mul_le_mul_of_nonneg_left book hA
    _ = _ := by ring

end YM.Integration.WilsonOriginalHomogeneousTube
