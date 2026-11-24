import YangMills.WilsonProof.NativeSupport.OPEMatching.PhysicalCoefficients
import YangMills.WilsonProof.NativeSupport.CorrelationMatching.Construction.Estimates
import YangMills.WilsonProof.NativeSupport.Solution.OPECoefficients
import YM.Integration.WilsonGraphPublishedReturnLaws

set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.WilsonFlashScoredChannels
open Function Set YangMills YM.OPE YM.OPE.Orbits YM.Answer.ContinuumLimit WilsonGraphPaperPublication
open WilsonGraphPublishedReturnLaws
open scoped Classical BigOperators
universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (p : ℕ → ℕ) (hp : StrictMono p)
private abbrev selectedVision := publicPick.{u} g hg (ElectedPublication.order p hp)
private abbrev electedReader := (selectedVision.{u} g hg p hp).pupil.P
private abbrev publishedHierarchy := hierarchy (selectedVision.{u} g hg p hp).pupil.last (electedReader.{u} g hg p hp)
private abbrev scoredMeasurement := CorrelationMatching.Construction.measurement (measurementOnPick.{u} g hg p hp)
section ReaderBasis
open YM YM.Spec
variable {G : GaugeGroup} {C : Family G.core} {order : Extraction.Order} {S : Table C.book}
variable (F : Final C order S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

theorem basis (h : ℕ) :
    ∃ basis : Module.Basis (Σ d : Fin (h+1), Q.channels d.val) ℂ ((hierarchy F Q).Field h),
      ∀ (d : Fin (h+1)) (c : Q.channels d.val),
        basis ⟨d,c⟩ = F.sector.derivatives.rise (Nat.le_of_lt_succ d.isLt) (Q.actor d.val c) := by
  classical
  let I := Σ d : Fin (h+1), Q.channels d.val
  let field : I → (hierarchy F Q).Field h := fun a => F.sector.derivatives.rise (Nat.le_of_lt_succ a.1.isLt) (Q.actor a.1.val a.2)
  let test (a : I) : (hierarchy F Q).Field h →ₗ[ℂ] ℂ :=
    (Q.basis a.1.val).coord a.2 ∘ₗ (Q.stratum a.1.val).subtype.leftInverse ∘ₗ Q.cutTest a.1.val h
  have delta (x y : I) : test x (field y) = if y = x then 1 else 0 := by
    obtain ⟨a,i⟩ := x
    obtain ⟨b,j⟩ := y
    change (Q.basis a.val).coord i ((Q.stratum a.val).subtype.leftInverse
      (Q.cutTest a.val h (F.sector.derivatives.rise (Nat.le_of_lt_succ b.isLt) (Q.basis b.val j).val))) = _
    rw [Q.cut_rise]
    by_cases eq : b = a
    · subst b
      rw [Q.test_fixes _ _ (Q.basis a.val j).property]
      erw [LinearMap.leftInverse_apply_of_inj (Q.stratum a.val).ker_subtype (Q.basis a.val j)]
      by_cases same : j = i
      · subst j
        simp [Module.Basis.coord_apply, Module.Basis.repr_self]
      · have different : (⟨a,j⟩ : I) ≠ ⟨a,i⟩ := fun he => same (Sigma.mk.inj_iff.mp he).2.eq
        simp [Module.Basis.coord_apply, Module.Basis.repr_self, different, Ne.symm same]
    · have grades : a.val ≠ b.val := fun same => eq (Fin.ext same.symm)
      have different : (⟨b,j⟩ : I) ≠ ⟨a,i⟩ := fun he => eq (congrArg Sigma.fst he)
      rw [Q.test_orthogonal _ _ _ (Q.basis b.val j).property grades, map_zero, map_zero, if_neg different]
  have independent : LinearIndependent ℂ field := by
    apply Fintype.linearIndependent_iff.mpr
    intro f hf j
    have ev := congrArg (test j) hf
    simp only [map_sum, map_smul, map_zero, delta, smul_eq_mul] at ev
    have single : (∑ x : I, if x = j then f x else 0) = f j := by
      calc
        _ = (if j = j then f j else 0) :=
          Finset.sum_eq_single j (fun b _ hb => if_neg hb)
            (fun absent => (absent (Finset.mem_univ j)).elim)
        _ = f j := if_pos rfl
    exact single.symm.trans (by simpa only [mul_ite, mul_one, mul_zero] using ev)
  have spanning : ⊤ ≤ Submodule.span ℂ (Set.range field) := by
    intro v _
    have single := Q.packet_single h h le_rfl v
    rw [F.sector.derivatives.arrival Q.continuum.laws.toSymmetric Q.lifts] at single
    rw [← single]
    unfold Reader.packet
    apply Submodule.sum_mem
    intro d _
    rw [← Q.assemble d.val (sole 0) (sole v : Labels _ fun _ : Unit => h) 0, map_sum]
    apply Submodule.sum_mem
    intro c _
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (⟨d,c⟩ : I)))
  exact ⟨Module.Basis.mk independent spanning, fun d c => Module.Basis.mk_apply _ _ _⟩

end ReaderBasis

theorem physical : OPEMatching.PhysicalCoefficients (scoredMeasurement.{u} g hg p hp) := by
  have laws := publicCoefficientLaws (selectedVision.{u} g hg p hp).pupil.last (electedReader.{u} g hg p hp)
  refine ⟨fun d w c x _ o => laws.multilinear d w c x o,
    fun slots a b x _ o shift same w c => laws.sameInputs slots a b x o shift same w c, ?_⟩
  exact basis (selectedVision.{u} g hg p hp).pupil.last (electedReader.{u} g hg p hp)

end YM.Integration.WilsonFlashScoredChannels
end
