import YM.Integration.WilsonOriginalPublicTrialPhaseAccumulated

/-! The exact flat value of the authenticated scalar at an arbitrary registered site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseFlat
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Guard Push Local Next.Foundations
open MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open OPE.Therm RG05Readout RG05Readout.Address
open WilsonOriginalPublicTrialPhaseUnit WilsonOriginalPublicTrialPhaseAccumulated
open scoped Classical BigOperators ContDiff
variable {G:Gauge}{F:Frame G 0}{n:Side}

theorem original (q:Coefficient F n)(o:Site n)(S:SectionData F)(A:Rep G n){hol:Hol G}
    (fmt:q.Format o hol A): q.density o S A 1=(A.eval 1:ℂ)*q.x 0:=by
  have he:flags A.p.threshold (1:Config G n)=∅:=UVNext.CouplingReset.flags_one _
  have hv (b):q.marked A b 1=0:=by
    unfold Coefficient.marked
    split
    next hp=>
      by_cases h:b=∅
      · rw [h,Finset.sum_empty]
      · obtain ⟨j,hj⟩:=Finset.nonempty_iff_ne_empty.mpr h
        obtain ⟨x,hx⟩:=(A.activities.forced j).inventory_ne
        have hY:x∈flags A.p.threshold (1:Config G n):= hp.2 ▸ mem_biUnion.mpr ⟨j,hj,hx⟩
        rw [he] at hY
        exact absurd hY (Finset.notMem_empty _)
    next _=>rfl
  have hz (i):q.maskedTerm A i 1=0:=by
    unfold Coefficient.maskedTerm masked Set.indicator
    split
    · exact fmt.identity_null i
    · rfl
  have core:F.core q.x=0:=by
    rw [vector F q.x,map_smul,Size.unit_core,smul_zero]
  have hs:S.places (F.scaled A.p.threshold⁻¹ (F.core q.x)) o 1=0:=by
    rw [core,map_zero,SectionData.places]
    exact congrFun ((S.eval_linear.mk' S.evaluate).map_zero) _
  unfold Coefficient.density Coefficient.exponentialEntry
  simp only [hv,hz,tsum_zero,mul_zero,add_zero]
  unfold masked Set.indicator
  split
  · rw [hs,add_zero]
  · rw [add_zero]

theorem settled (q:Coefficient F n)(o:Site n)(S:SectionData F)(A:Rep G n){hol:Hol G}
    (fmt:q.Format o hol A)(z:ℂ): (row q o S A z).1 1=(A.eval 1:ℂ)*z:=by
  have fmt':(centered q).Format o hol A:=by
    obtain ⟨s,t,u,v,h,x,a,b,g⟩:=fmt
    exact ⟨s,t,u,v,h,x,a,b,g⟩
  change (centered q).density o S A 1+z*(A.eval 1:ℂ)=_
  rw [original _ _ _ _ fmt']
  change (A.eval 1:ℂ)*0+z*(A.eval 1:ℂ)=_
  ring

end YM.Integration.WilsonOriginalPublicTrialPhaseFlat
end
