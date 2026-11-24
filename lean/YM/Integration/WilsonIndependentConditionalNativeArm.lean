import YM.Integration.WilsonIndependentConditionalNativeLinks

/-! The native zero-mean upper mark is the actual first channel on all
link coordinates. This includes scalar input and preserves its carried fronts. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalNativeArm
open Function Lattice RG WilsonCoeffUV Laurent Bloch Metric WilsonCoeffUV.Blue
open Work.F08 WilsonCoeffUV.Bank Wilson Tree Exterior WilsonCoeffUV.Mer WilsonCoeffUV.Soil Precision Embroider
open RegulatorIR RegulatorIR.Prim RegulatorIR.Oracle RegulatorIR.Step RegulatorIR.Budget RegulatorIR.Budget.Packet
open WilsonIndependentConditionalCoordinateHeat WilsonIndependentConditionalNativeLinks
open scoped BigOperators Matrix Classical
variable {G:Gauge}{r:ℕ}

private theorem delta {α β:Type}[Fintype α][DecidableEq α](F:Packet (Cloth α) r)(y:Tuple (Cloth α) r):
    reflectCut (upper (β:=β) 1 0) F (pierL ∘ y)=F y:=by
  rw [climb_cut]
  change (∑' z:Tuple (Cloth α) r,(∏ i,(1:ropes Cover α α) (z i) (y i)) • F z)=_
  rw [tsum_eq_single y]
  · simp
  · intro z hn
    obtain ⟨i,hi⟩:=Function.ne_iff.mp hn
    have z0:∏i,(1:ropes Cover α α) (z i) (y i)=0:=Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [z0,zero_smul]

private theorem missing {α β:Type}[Fintype α][DecidableEq α](F:Packet (Cloth α) r)
    (v:Tuple (Cloth (α⊕β)) r)(i:Fin r)(b:Cloth β)(h:v i=pierR b):
    reflectCut (upper 1 0) F v=0:=by
  rw [climb_cut]
  have no (z:Tuple (Cloth α) r):(∏i,(upper (β:=β) 1 0) (z i) (v i)) • F z=0:=by
    have z0:∏i,(upper (β:=β) 1 0) (z i) (v i)=0:=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h,handR];rfl)
    rw [z0,zero_smul]
  simp_rw [no,tsum_zero]

theorem original (P:Patch)(F:Pal ℝ (YForest G))(e r):
    row (joint G P) (slidesJ P 0 F e r)=offer (Function.Embedding.inl:Foot G↪KFoot G) (row (coarse G) (F e r)):=by
  funext z
  by_cases h:z∈Set.range (acrossT (Function.Embedding.inl:Foot G↪KFoot G))
  · obtain ⟨v,rfl⟩:=h
    rw [offer_eq]
    change reflectCut (upper 1 0) _ (pierL ∘ (fine G P ∘ v))=_
    rw [delta]
    change F e r ((panel P.L (Hooks G)) ∘ (fine G P ∘ v))=F e r (coarse G ∘ v)
    apply congrArg
    funext i;exact fine_link P (v i)
  · rw [offer_zero _ h]
    have has:∃i b,z i=Sum.inr b:=by
      by_contra none
      have exist (i):∃x,z i=Sum.inl x:=by
        cases eq:z i with
        | inl x=>exact ⟨x,rfl⟩
        | inr b=>exact (none ⟨i,b,eq⟩).elim
      choose v hv using exist
      exact h ⟨v,funext fun i=>(hv i).symm⟩
    obtain ⟨i,b,hb⟩:=has
    apply missing _ (joint G P ∘ z) i (coarse G b)
    rw [Function.comp_apply,hb];rfl

end YM.Integration.WilsonIndependentConditionalNativeArm
