import YM.Integration.WilsonOriginalPublicTrialPhaseSettled
import YM.Integration.WilsonOriginalPublicTrialPhaseWhole

/-! The genuine occupied and masked regular payments for every copy at the terminal. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseVault
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Marker Ac
open Planned.GuardedAtom Guard Push Local Next.Foundations
open MergeProof MergeProof.Accent PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open RG05Readout RG05Readout.Address
open WilsonOriginalPublicTrialPhaseAccumulated WilsonOriginalPublicTrialPhaseUnit
open scoped Classical BigOperators ContDiff
variable {G:Gauge}{F:Frame G 0}{n:Side}

theorem parts (A:Rep G n)(S:SectionData F)(q:Coefficient F n)(o:Site n)
    {κ r:ℝ}(rem:q.remBound o A κ r)(hk:κ≤1)(U:Config G n):
    ‖(row q o S A 0).2.1 U‖≤r ∧
      (∑ b,‖profile A.activities (row q o S A 0).2.2 b U‖)≤r:=by
  obtain ⟨reg,hard⟩:= tendrils A o q U rem hk
  refine ⟨?_,hard⟩
  change ‖(centered q).exponentialEntry o S A U+0‖≤r
  rw [add_zero,Coefficient.exponentialEntry]
  have word:S.places (F.scaled A.p.threshold⁻¹ (F.core (centered q).x)) o U=0:=by
    change S.places (F.scaled A.p.threshold⁻¹ (F.core 0)) o U=0
    rw [map_zero,map_zero,SectionData.places]
    exact congrFun ((S.eval_linear.mk' S.evaluate).map_zero) _
  unfold masked Set.indicator
  split
  · rw [word]
    change ‖0+0+∑'i,q.maskedTerm A i U‖≤r
    simpa using reg
  · change ‖0+0+∑'i,q.maskedTerm A i U‖≤r
    simpa using reg

theorem original {V:Type}[Fintype V](A:Rep G n)(S:SectionData F)(q:V → Coefficient F n)(o:V→Site n)
    {κ r w:ℝ}(rem:∀v,(q v).remBound (o v) A κ r)(hk:κ≤1)(hw:0≤w):
    Vault (fun _:V=>w) (fun v=>(row (q v) (o v) S A 0).2.1)
      (fun v=>profile A.activities (row (q v) (o v) S A 0).2.2) (w*r) (w*r):=by
  refine ⟨fun v U=>mul_le_mul_of_nonneg_left (parts A S (q v) (o v) (rem v) hk U).1 hw,?_⟩
  intro v U
  rw [←Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (parts A S (q v) (o v) (rem v) hk U).2 hw

end YM.Integration.WilsonOriginalPublicTrialPhaseVault
end
