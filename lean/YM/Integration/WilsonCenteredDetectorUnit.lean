import YM.Integration.WilsonCenteredCaptureUnit
import YM.Push.LOCAL_SPLITTING.Comparison

/-! On the unchanged Wilson vacuum the order-zero probe of a truly
formatted outgoing coordinate is its complete physical flat reading.
Only the positive-order probes require differentiated estimates. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredDetectorUnit
open Finset Lattice RG Wilson Source Labels Push.Local Next.Foundations Marker QuadraticLocal
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}
    {A : Hol G} {T : SectionData F} {P : Rep G n} {o : Site n}

theorem flatProbe (C : Coefficient F n) (form : C.Format o A P) (sound : T.Sound A)
    (p : Probe G d) (zero : p.2.val = 0) :
    runProbe F p C.x = (P.eval (1 : Config G n):ℂ)⁻¹ * C.density o T P 1 := by
  have clear : flags P.p.threshold (1 : Config G n) = ∅ := UVNext.CouplingReset.flags_one P.p
  have tail (k : Finset ℕ) : C.marked P k 1 = 0 := by
    unfold Coefficient.marked
    split
    next adm =>
      have empty : k = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨y,hy⟩ := (P.activities.forced i).inventory_ne
        have hf : y ∈ flags P.p.threshold (1:Config G n) :=
          adm.2 ▸ Finset.mem_biUnion.mpr ⟨i,hi,hy⟩
        rw [clear] at hf
        exact notMem_empty y hf
      simp [empty]
    rfl
  have quiet (i : ℕ) : C.maskedTerm P i 1 = 0 := by
    rw [Coefficient.maskedTerm,masked_eq _ _ _ _ (one_healthy _ _ P.p.threshold_pos.le),form.identity_null]
  have entry : C.exponentialEntry o T P 1 = primary T o P.p.threshold C.x 1 := by
    unfold Coefficient.exponentialEntry
    simp_rw [quiet]
    rw [tsum_zero,add_zero]
    rfl
  have denom : (P.eval (1:Config G n):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr WilsonCenteredCaptureUnit.physicalDenominator.ne'
  rw [Coefficient.density]
  simp_rw [tail]
  rw [tsum_zero,mul_zero,add_zero,←mul_assoc,inv_mul_cancel₀ denom,one_mul,entry,
    presented_primary o sound C.x 1 (one_healthy _ _ P.p.threshold_pos.le)]
  have flat := (sound.projects (F.scaled P.p.threshold⁻¹ C.x) p.1).2.2 0 (Nat.zero_le _)
  have hz : scaleJet p.1 0 = 0 := by
    funext i
    simp [scaleJet]
  change iteratedDeriv 0 (fun t=>T.evaluate (F.scaled P.p.threshold⁻¹ C.x) (A.links d p.1 t)) 0 =
    iteratedDeriv 0 (fun t=>Labels.read (scaleJet p.1 t) (F.coords.symm (F.scaled P.p.threshold⁻¹ C.x)).val) 0 at flat
  rw [iteratedDeriv_zero,iteratedDeriv_zero,A.flat,hz,read_frame_scaled,smul_zero] at flat
  rw [runProbe_eq,zero,iteratedDeriv_zero,hz]
  exact flat.symm

/-- Use one aggregate signed Wilson flat comparison at every zero-order
probe. The measured intermediate primary survives inside both coordinates. -/
theorem hearing (C B : Coefficient F n) (forms : C.Format o A P) (file : B.Format o A P)
    (sound : T.Sound A) {flat high : ℝ} (hflat : 0 ≤ flat)
    (unit : ‖(P.eval (1:Config G n):ℂ)⁻¹ * (C.density o T P 1 - B.density o T P 1)‖ ≤ flat)
    (partials : ∀ p ∈ tests F, 0 < p.2.val → ‖runProbe F p (C.x-B.x)‖ ≤ high) :
    F.coeffSize (C.x-B.x) ≤ testPrice F * max flat high := by
  apply (probe_budget F).choose_spec.choose_spec.2 _ _ (hflat.trans (le_max_left ..))
  intro p hp
  by_cases h : p.2.val = 0
  · rw [map_sub,flatProbe C forms sound p h,flatProbe B file sound p h,←mul_sub]
    exact unit.trans (le_max_left ..)
  exact (partials p hp (Nat.pos_of_ne_zero h)).trans (le_max_right ..)

end YM.Integration.WilsonCenteredDetectorUnit
