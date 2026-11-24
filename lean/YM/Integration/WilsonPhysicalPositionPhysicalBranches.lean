import YM.Integration.WilsonPhysicalPositionBornCandidates

/-! One finite menu of admissible Born limits for every bounded physical
scale ratio, purchased on the original physical hierarchy. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionPhysicalBranches
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPhysicalPositionBornCandidates
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (F:Final C f S)(J:ℝ→tower S)

theorem original (lead:Leading F J)(V:Store G)(d:ℕ):
    ∃ B:ℝ, 1≤B ∧ ∃ menu:Finset (MoveSpace G d),∀{I:Type*}{l:Filter I}[NeBot l]
      {r t:I→ℝ}{c u:ℝ},0<c→0<u→Tendsto r l trail→Tendsto t l (𝓝 u)→
      (∀ᶠ i in l,t i∈Icc c 1)→∀(pos:∀i,0<t i)(a:MoveSpace G d),
      (∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l
        (𝓝 (operator C a v)))→a∈menu:=by
  obtain ⟨B,hB,bought⟩:=Frame.comparison F d J lead
  have fin:=finite C V d B
  refine ⟨B,hB,fin.toFinset,?_⟩
  intro I l hl r t c u hc hu hr ht hi pos a conv
  apply fin.mem_toFinset.mpr
  refine ⟨WilsonPhysicalPositionBornTransition.original F J lead hr hu ht pos a conv,?_,?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hB)
    intro v
    apply le_of_tendsto (conv v).norm
    filter_upwards [hr.eventually (bought c hc),hi] with i h h'
    exact (h _ h').1 v
  intro v
  apply ge_of_tendsto ((tendsto_const_nhds (x:=B)).mul (conv v).norm)
  filter_upwards [hr.eventually (bought c hc),hi] with i h h'
  let Z:=Frame.cocycle d J (r i) (t i) (pos i)
  change ‖v‖≤B*‖Z v‖
  calc
    ‖v‖ = ‖Z.symm (Z v)‖ := by rw [LinearEquiv.symm_apply_apply]
    _ ≤ B*‖Z v‖ := (h (t i) h').2 (Z v)

end YM.Integration.WilsonPhysicalPositionPhysicalBranches
end
