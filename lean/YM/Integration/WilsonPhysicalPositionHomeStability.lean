import YM.Integration.WilsonPhysicalPositionHomeDilation

/-! The original position Jacobian bounds the error of any prescribed
bounded-ratio transition on its already selected branch. Its entire right
side evaluates the original same-home determining tests at the dilated
positions, including the lower and unit entries. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionHomeStability
open Function Set Filter Spec Table Extraction Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(J:ℝ→tower S)

theorem runs {I:Type*}{l:Filter I}{r τ:I→ℝ} (hr:Tendsto r l trail)(ht:∀ᶠi in l,τ i ∈ Icc (1:ℝ) 2):
    Tendsto (fun i=>r i*τ i) l trail:=by
  apply tendsto_def.mpr
  intro U hU
  filter_upwards [hr.eventually (WilsonPhysicalPositionHomeDilation.window (p:=fun a=>a∈U) hU),ht] with i hi ht'
  exact hi.2 _ ht'

theorem original (lead:Leading F J)(V:Store G)(d:ℕ){I:Type*}{l:Filter I}{r τ:I→ℝ}
    (hr:Tendsto r l trail)(ht:∀ᶠi in l,τ i∈Icc (1:ℝ) 2)(A:I→Change G d)
    (branch:Tendsto (fun i=>guide G d (A i)) l (𝓝 0)):
    ∃ L:ℝ,0≤L ∧ ∀ᶠ i in l,
      let ρ:=r i*τ i
      let H:=(WilsonPhysicalPositionHomeDilation.arm J (r i) ρ d).toLinearMap ∘ₗ stand (A i)
      ‖guide G d (WilsonPositionPrescribedScreen.correction F J V d ρ) - guide G d (A i)‖ ≤
        L*‖guide G d ((V.measure d).D (recruit H
          (WilsonPhysicalPositionHomeDilation.samples F J (r i) (τ i) d))) -
          guide G d ((V.measure d).D (reference G d))‖:=by
  let D:=V.survey d
  let ρ:=fun i=>r i * τ i
  let P:=WilsonPositionPrescribedScreen.hierarchy F J d
  have reaches:Tendsto ρ l trail:=runs hr ht
  have prices:Tendsto (fun i=>D.purse (P (ρ i))) l (𝓝 D.opening.1):=
    (WilsonPositionPrescribedScreen.warm F J lead V d).comp reaches
  obtain ⟨L,pos,bill⟩:=WilsonPositionPrescribedStability.residual D (V.prepared d) prices branch
  refine ⟨L,pos,?_⟩
  have hrpos:∀ᶠ i in l,0<r i:=hr.eventually self_mem_nhdsWithin
  filter_upwards [bill,hrpos,ht] with i hi rpos tbound
  have fact:=WilsonPhysicalPositionHomeDilation.full F J rpos (lt_of_lt_of_le zero_lt_one tbound.1) d
  dsimp only
  rw [←recruits_comp,←fact]
  change ‖guide G d (D.firstPass _ (P (ρ i)))-guide G d (A i)‖≤_
  rw [D.guid]
  simpa only [Fray.opening,D.way,Fray.box,LinearEquiv.symm_apply_apply,map_zero,stand0,Screen.recruit_one] using hi

end YM.Integration.WilsonPhysicalPositionHomeStability
end
