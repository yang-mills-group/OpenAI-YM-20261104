import YM.Integration.WilsonMeasuredPublicEntranceCheapField
import YM.Integration.WilsonThermometerHostedLamp

/-! Reissue only the genuine primary and masked regular functions on a
receiver of the same Wilson budget. The registered forced entries stay on
their original host. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceSoftHost
open Function Finset Lattice Wilson RG Source Labels
open WilsonPhysicalMarkedDefect.RegularProjection
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d}
    (q : Coefficient F n) (W P : Rep G n) (same : P.p=W.p)
    (o : Site n) (A : Hol G) (S : SectionData F)

include same in
theorem original {κ M : ℝ} (witness : q.Format o A W) (paid : q.remBound o W κ M) :
    (soft q).Format o A P ∧ (soft q).remBound o P κ M ∧
    ∀U,(soft q).exponentialEntry o S P U=q.exponentialEntry o S W U := by
  refine ⟨⟨fun i => by simpa only [soft,same] using witness.smooth i,witness.origin,
    witness.identity_null,witness.projects,?_,?_,?_,?_,?_⟩,?_,?_⟩
  · exact fun _ _ nz => False.elim (nz rfl)
  · exact fun _ nz => False.elim (nz rfl)
  · exact fun _ _ _ => rfl
  · exact fun _ _ _ _ _ => rfl
  · exact fun _ => measurable_const
  · obtain ⟨a,b,ha,hb,total,k,regular,_⟩ := paid
    refine ⟨a,0,ha,le_rfl,by linarith,k,?_,fun _ => 0,?_,fun _ => ⟨le_rfl,by simp [soft]⟩⟩
    · simpa only [soft,same] using regular
    · simp [SumBudget,BudgetPoint.mass]
  · intro U
    simp only [Coefficient.exponentialEntry,Coefficient.maskedTerm,same,soft]

end YM.Integration.WilsonMeasuredPublicEntranceSoftHost
end
