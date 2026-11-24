import YM.Integration.WilsonMeasuredPublicEntranceBranchGap

/-! The oriented action ray modulo the vacuum is closed on the actual finite
space. Neither of its scalar representatives needs a preassigned upper bound. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceActionLimit
open Function Filter Set
open scoped Classical Topology
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℝ E]

theorem original {I:Type*}{l:Filter I}[NeBot l]{z:I→E}{v p one:E}
    (converges:Tendsto z l (𝓝 v))
    (given:∀ᶠ i in l,∃s:ℝ,0 ≤ s ∧ ∃c:ℂ,z i=s • p+c • one):
    ∃s:ℝ,0 ≤ s ∧ ∃c:ℂ,v=s • p+c • one:=by
  let M:Submodule ℂ E:=Submodule.span ℂ {one}
  let A:=M.restrictScalars ℝ
  have unit:one∈M:=Submodule.subset_span (Set.mem_singleton _)
  have closed:IsClosed (A:Set E):=A.closed_of_finiteDimensional
  by_cases member:p∈A
  · have belongs:v∈A:=closed.mem_of_tendsto converges (given.mono fun i h=>by
      obtain ⟨s,_,c,rfl'⟩:=h
      rw [rfl']
      exact A.add_mem (A.smul_mem s member) (M.smul_mem c unit))
    obtain ⟨c,eq⟩:=Submodule.mem_span_singleton.mp (show v∈M from belongs)
    exact ⟨0,le_refl _,c,by simpa only [zero_smul,zero_add] using eq.symm⟩
  let B:=Module.Free.chooseBasis ℝ (E ⧸ A)
  have found:∃j,B.coord j (A.mkQ p)≠0:=by
    by_contra! none
    apply member
    apply (Submodule.Quotient.mk_eq_zero A).mp
    apply B.repr.injective
    ext j
    rw [map_zero,Finsupp.zero_apply]; exact none j
  obtain ⟨j,hj⟩:=found
  let g:E→ₗ[ℝ]ℝ:=(B.coord j (A.mkQ p))⁻¹ • (B.coord j).comp A.mkQ
  have value:g p=1:=inv_mul_cancel₀ hj
  have quiet(w:E)(hm:w∈A):g w=0:=by
    change (B.coord j (A.mkQ p))⁻¹ * B.coord j (A.mkQ w)=0
    have eq:A.mkQ w=0:=(Submodule.Quotient.mk_eq_zero A).mpr hm
    rw [eq,map_zero,mul_zero]
  have read:∀ᶠ i in l,0 ≤ g (z i) ∧ z i-g (z i)•p∈A:=given.mono fun i h=>by
    obtain ⟨s,hs,c,eq⟩:=h
    have hc:c • one ∈ A:=M.smul_mem c unit
    have live:g (z i)=s:=by rw [eq,map_add,map_smul,value,quiet _ hc,add_zero,smul_eq_mul,mul_one]
    refine ⟨live.symm ▸ hs,?_⟩
    rw [live,eq,add_sub_cancel_left]; exact hc
  have tends:=g.continuous_of_finiteDimensional.continuousAt.tendsto.comp converges
  have hs:0 ≤ g v:=ge_of_tendsto tends (read.mono fun _ h=>h.1)
  have rem:v-g v • p∈A:=closed.mem_of_tendsto (converges.sub (tends.smul tendsto_const_nhds))
    (read.mono fun _ h=>h.2)
  obtain ⟨c,eq⟩:=Submodule.mem_span_singleton.mp (show v-g v • p∈M from rem)
  exact ⟨g v,hs,c,by rw [eq];abel⟩
end YM.Integration.WilsonMeasuredPublicEntranceActionLimit

